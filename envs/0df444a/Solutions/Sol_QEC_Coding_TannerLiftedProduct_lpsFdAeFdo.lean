-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsFdAeFdo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:21:38.602456+00:00
-- url     : https://prove2.me/submissions/ff4533f6-9fc4-4bad-9741-965d3b656885

import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Countable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsBoundaryNull

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution : ModularGroup.fd =ᵐ[volume] ModularGroup.fdo := by
  apply ae_eq_set.mpr
  exact ⟨lpsBoundaryNull, by simp [sdiff_eq_empty.mpr ModularGroup.fdo_subset_fd]⟩
end QEC.Coding.TannerLiftedProduct
