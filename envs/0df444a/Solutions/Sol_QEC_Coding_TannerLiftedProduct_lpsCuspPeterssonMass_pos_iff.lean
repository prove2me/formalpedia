-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonMass_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:09.937124+00:00
-- url     : https://prove2.me/submissions/433d0949-a0bb-4ac6-a3d8-f044f3899a16

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.InnerProductSpace.Defs
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonMass_eq_zero_iff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_nonneg


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    0<(∫τ in ModularGroup.fd,lpsCuspPeterssonDensity N f τ) ↔ f≠0 := by
  have hp : 0≤(∫τ in ModularGroup.fd,lpsCuspPeterssonDensity N f τ) :=
    integral_nonneg (lpsCuspPeterssonDensity_nonneg N f)
  rw [lt_iff_le_and_ne, and_iff_right hp, ne_comm, ne_eq, lpsCuspPeterssonMass_eq_zero_iff]
end QEC.Coding.TannerLiftedProduct
