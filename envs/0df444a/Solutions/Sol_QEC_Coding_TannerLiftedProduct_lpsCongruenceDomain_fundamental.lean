-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCongruenceDomain_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:24:45.680431+00:00
-- url     : https://prove2.me/submissions/c6e66c6b-924d-4f85-8ef2-d95898673c13

import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Countable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCongruenceDomain_nullMeasurable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCongruenceDomain_covers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCongruenceDomain_aedisjoint

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup lpsEffectiveModularGroup) :
    IsFundamentalDomain H (lpsCongruenceDomain H) volume := by
  apply IsFundamentalDomain.mk'' (lpsCongruenceDomain_nullMeasurable H)
  · exact Eventually.of_forall (lpsCongruenceDomain_covers H)
  · exact lpsCongruenceDomain_aedisjoint H
  · intro h
    exact (lpsEffectiveMeasurePreserving (h : lpsEffectiveModularGroup)).quasiMeasurePreserving
end QEC.Coding.TannerLiftedProduct
