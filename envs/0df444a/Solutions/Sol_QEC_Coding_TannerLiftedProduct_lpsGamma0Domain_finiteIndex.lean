-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0Domain_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:51:12.078573+00:00
-- url     : https://prove2.me/submissions/0facac56-a222-41d2-8aca-955a71b1e1dc

import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Countable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveGamma0_index

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] :
    (lpsEffectiveGamma0 N).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff,lpsEffectiveGamma0_index]
  exact Subgroup.FiniteIndex.index_ne_zero
end QEC.Coding.TannerLiftedProduct
