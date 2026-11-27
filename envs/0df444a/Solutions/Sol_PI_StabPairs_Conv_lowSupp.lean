-- Prove2me | solution 1 for PI.StabPairs.Conv.lowSupp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:37:30.772491+00:00
-- url     : https://prove2.me/submissions/5575c1b3-505e-475e-8ce7-d3dafbcae4e0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConvAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast

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
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : ℕ) (ha : a ≤ r) (x : Fin (r + 1) → ℂ)
    (hx : ∀ c : Fin (r + 1), a ≤ c.val → x c = 0) (i : Fin (2 * r + k + 1)) (hi : a ≤ i.val) :
    (∑ c, x c • fvec k r z c) i = 0 := by
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : a ≤ c.val
  · simp [hx c hc]
  · have hcr : c.val < r := by omega
    have hne : i ≠ eI k r ⟨c.val, hcr⟩ := by
      intro e; rw [Fin.ext_iff] at e; simp [eI] at e; omega
    simp [fvec, hcr, bvec, Pi.single_apply, hne]
end PI.StabPairs.Conv
