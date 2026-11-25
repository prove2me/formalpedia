-- Prove2me | solution 1 for PI.StabPairs.Conv.herm_bvec_fvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:25:45.791693+00:00
-- url     : https://prove2.me/submissions/004b2ff8-fc17-44dd-9a1d-51b7771d9765

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_HermBvecFvec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairs PI.StabPairs.Conv
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW
namespace PI.StabPairs.Conv
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1))
    (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) (a : Fin (r + 1)) (ha : a.val < r) :
    herm (Hpk k r) (bvec j) (fvec k r z a) = 0 := by
  have hH : ∀ (e j : Fin (2 * r + k + 1)), e.val < r → r ≤ j.val → j.val ≤ r + k →
      Hpk k r e j = 0 := by
    intro e j he hj1 hj2
    unfold Hpk
    rw [if_neg (fun h => absurd h.2 (by omega)), if_neg (fun h => absurd h.1 (by omega)),
      if_neg (fun h => absurd h.1 (by omega))]
  have hf : fvec k r z a = bvec (eI k r ⟨a.val, ha⟩) := by
    unfold fvec
    rw [dif_pos ha]
  rw [hf]
  have h1 : herm (Hpk k r) (bvec j) (bvec (eI k r ⟨a.val, ha⟩)) = Hpk k r (eI k r ⟨a.val, ha⟩) j := by
    simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]
  rw [h1]
  exact hH _ _ ha hj1 hj2
end PI.StabPairs.Conv
