-- Prove2me | solution 1 for PI.StabPairsW.fvec_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:27:47.305706+00:00
-- url     : https://prove2.me/submissions/e165ed75-06d2-438e-aede-814f64435a3c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV

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
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : Fin (r + 1)) (a : Fin r) :
    fvec k r z c (eI k r a) = if c.val = a.val then 1 else 0 := by
  have ha := a.isLt
  have hc := c.isLt
  unfold fvec
  by_cases h : c.val < r
  · rw [dif_pos h]
    simp only [bvec, Pi.single_apply, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [dif_neg h, hz (eI k r a) (Or.inl (by simp [eI])), if_neg (by omega)]
end PI.StabPairsW
