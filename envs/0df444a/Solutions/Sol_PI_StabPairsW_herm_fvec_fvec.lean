-- Prove2me | solution 1 for PI.StabPairsW.herm_fvec_fvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:35.50416+00:00
-- url     : https://prove2.me/submissions/259d9e7c-d595-46f7-a939-d64a2a686e68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_herm_e
import Theorems.Thm_PI_StabPairsW_fvec_esI
import Theorems.Thm_PI_StabPairsW_herm_Hpk_fvec_eq_ite

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
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (a b : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z b) (fvec k r z a) =
      if a = Fin.last r ∧ b = Fin.last r then herm (Hpk k r) z z else 0 := by
  by_cases ha : a.val < r
  · have hne : a ≠ Fin.last r := fun h => by rw [h] at ha; simp at ha
    rw [if_neg (fun h => hne h.1)]
    rw [show fvec k r z a = bvec (eI k r ⟨a.val, ha⟩) by simp [fvec, ha], herm_e, fvec_esI z hz]
  · have heq : a = Fin.last r := Fin.ext (by have := a.isLt; simp; omega)
    rw [show fvec k r z a = z by simp [fvec, ha], herm_Hpk_fvec_eq_ite z hz b]
    simp [heq]
end PI.StabPairsW
