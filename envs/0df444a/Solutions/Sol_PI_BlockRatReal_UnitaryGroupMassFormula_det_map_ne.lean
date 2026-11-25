-- Prove2me | solution 1 for PI.BlockRatReal.UnitaryGroupMassFormula.det_map_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:58.468318+00:00
-- url     : https://prove2.me/submissions/c1a18a84-7530-4f03-8cc4-085ae2452a07

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_NuOfAntitone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.BlockRatReal PI.BlockRatReal.UnitaryGroupMassFormula
namespace PI.BlockRatReal.UnitaryGroupMassFormula
theorem _root_.solution {LL : Type} [Field LL] (embLL : LL →+* ℂ) {k : ℕ} (M0 : GL (Fin k) LL) :
    (M0.1.map embLL).det ≠ 0 := by
  have hu : IsUnit M0.1.det := (Matrix.isUnit_iff_isUnit_det _).mp M0.isUnit
  have hm := RingHom.map_det embLL M0.1
  rw [RingHom.mapMatrix_apply] at hm
  rw [← hm]
  exact (map_ne_zero embLL).mpr hu.ne_zero
end PI.BlockRatReal.UnitaryGroupMassFormula
