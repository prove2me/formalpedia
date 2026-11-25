-- Prove2me | solution 1 for PI.StabPairsW.fvec_esI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:27:52.395801+00:00
-- url     : https://prove2.me/submissions/ca6e37e9-aea2-4151-a910-c7e6f10271b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_z_esI

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
    fvec k r z c (esI k r a) = 0 := by
  have ha := a.isLt
  unfold fvec
  by_cases h : c.val < r
  · rw [dif_pos h]
    simp only [bvec, Pi.single_apply, eI, esI, Fin.ext_iff]
    rw [if_neg (by omega)]
  · rw [dif_neg h]
    exact z_esI z hz a
end PI.StabPairsW
