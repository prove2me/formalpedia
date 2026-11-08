-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0Domain_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:51:10.334664+00:00
-- url     : https://prove2.me/submissions/f136c6b6-f8ab-4cf7-8985-520ff9e30830

import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Countable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCongruenceDomain_fundamental

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) :
    IsFundamentalDomain (lpsEffectiveGamma0 N)
      (lpsCongruenceDomain (lpsEffectiveGamma0 N)) volume :=
  lpsCongruenceDomain_fundamental (lpsEffectiveGamma0 N)
end QEC.Coding.TannerLiftedProduct
