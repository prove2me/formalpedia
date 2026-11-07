-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:08.699491+00:00
-- url     : https://prove2.me/submissions/1c22648e-cf44-4952-a0d7-5288ad9bb0d6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.InnerProductSpace.Defs
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ‖lpsCuspPeterssonPairing N f g‖^2 ≤
      (lpsCuspPeterssonPairing N f f).re*(lpsCuspPeterssonPairing N g g).re := by
  let : InnerProductSpace.Core ℂ
    (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) := lpsCuspPeterssonCore N
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜:=ℂ) f g
  rw [InnerProductSpace.Core.norm_inner_symm g f] at h
  change ‖lpsCuspPeterssonPairing N f g‖*‖lpsCuspPeterssonPairing N f g‖ ≤ (lpsCuspPeterssonPairing N f f).re*(lpsCuspPeterssonPairing N g g).re at h
  simpa only [pow_two] using h
end QEC.Coding.TannerLiftedProduct
