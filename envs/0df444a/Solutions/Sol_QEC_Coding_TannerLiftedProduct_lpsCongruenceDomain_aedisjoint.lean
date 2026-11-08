-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCongruenceDomain_aedisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:23:48.748295+00:00
-- url     : https://prove2.me/submissions/89368f06-183b-4865-8adc-98be52b58b5b

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
theorem _root_.solution (H : Subgroup lpsEffectiveModularGroup)
    (h : H) (hh : h ≠ 1) :
    AEDisjoint volume (h • lpsCongruenceDomain H) (lpsCongruenceDomain H) := by
  simp only [lpsCongruenceDomain,smul_set_iUnion,AEDisjoint.iUnion_left_iff,AEDisjoint.iUnion_right_iff]
  intro d c
  change AEDisjoint volume ((h : lpsEffectiveModularGroup) •
    ((Quotient.out c)⁻¹ • ModularGroup.fd)) ((Quotient.out d)⁻¹ • ModularGroup.fd)
  rw [←mul_smul]
  apply lpsEffectiveFundamentalDomain.aedisjoint
  intro he
  have hm : (Quotient.out d)⁻¹ * Quotient.out c = (h : lpsEffectiveModularGroup) := by
    have := congrArg (fun x : lpsEffectiveModularGroup => x * Quotient.out c) he
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using this.symm
  have hc : d = c := by
    rw [←Quotient.out_eq' d,←Quotient.out_eq' c,QuotientGroup.eq,hm]
    exact h.property
  subst c
  have hh' : (h : lpsEffectiveModularGroup) = 1 := by
    rw [hm.symm,inv_mul_cancel]
  exact hh (Subtype.ext hh')
end QEC.Coding.TannerLiftedProduct
