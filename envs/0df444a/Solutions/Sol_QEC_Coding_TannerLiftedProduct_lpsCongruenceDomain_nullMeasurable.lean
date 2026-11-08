-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCongruenceDomain_nullMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:23:21.904771+00:00
-- url     : https://prove2.me/submissions/e916acf1-0fd4-492e-a28c-bc74f190847a

import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Countable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveFundamentalDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveCosets_countable
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsEffectiveCosets_countable

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup lpsEffectiveModularGroup) :
    NullMeasurableSet (lpsCongruenceDomain H) volume := by
  letI : Countable (lpsEffectiveModularGroup ⧸ H) := lpsEffectiveCosets_countable H
  apply NullMeasurableSet.iUnion
  intro c
  exact lpsEffectiveFundamentalDomain.nullMeasurableSet_smul (Quotient.out c)⁻¹
end QEC.Coding.TannerLiftedProduct
