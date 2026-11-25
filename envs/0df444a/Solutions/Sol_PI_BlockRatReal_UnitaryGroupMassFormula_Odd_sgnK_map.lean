-- Prove2me | solution 1 for PI.BlockRatReal.UnitaryGroupMassFormula.Odd.sgnK_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:53.875692+00:00
-- url     : https://prove2.me/submissions/4c2cac28-34fa-4e40-8848-f7caedabb1d7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_OddDualWeylFactorization
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_MapDetGenM
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.BlockRatReal PI.BlockRatReal.UnitaryGroupMassFormula PI.BlockRatReal.UnitaryGroupMassFormula.Odd
open PI.OddDualWeyl
namespace PI.BlockRatReal.UnitaryGroupMassFormula.Odd
theorem _root_.solution {LL : Type} [Field LL] (φ : LL →+* ℂ) (m : ℕ) : φ (sgnK LL m) = sgnK ℂ m := by
  simp only [sgnK]
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, revCol, Matrix.submatrix_apply, id,
    Matrix.one_apply]
  split_ifs <;> simp
end PI.BlockRatReal.UnitaryGroupMassFormula.Odd
