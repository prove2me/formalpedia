-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveGamma0_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:20:12.794818+00:00
-- url     : https://prove2.me/submissions/ab27daf2-ad0f-4817-92a1-0c78d6af42a0

import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Countable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) :
    (lpsEffectiveGamma0 N).index = (CongruenceSubgroup.Gamma0 N).index :=
  Nat.card_congr (lpsEffectiveGamma0CosetEquiv N).symm
end QEC.Coding.TannerLiftedProduct
