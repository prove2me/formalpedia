-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCongruenceDomain_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:20:14.470819+00:00
-- url     : https://prove2.me/submissions/9209b4bb-3d12-453d-9674-6d2a80dc21d4

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
theorem _root_.solution (H : Subgroup lpsEffectiveModularGroup) (τ : ℍ) :
    ∃h : H,h • τ ∈ lpsCongruenceDomain H := by
  obtain ⟨g,hg⟩ := ModularGroup.exists_smul_mem_fd τ
  let g' : lpsEffectiveModularGroup := (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict g
  let c : lpsEffectiveModularGroup ⧸ H := QuotientGroup.mk g'
  let r := Quotient.out c
  have hc : QuotientGroup.mk r = QuotientGroup.mk g' := Quotient.out_eq' c
  have hk : r⁻¹*g' ∈ H := QuotientGroup.eq.mp hc
  let h : H := ⟨r⁻¹*g',hk⟩
  refine ⟨h,Set.mem_iUnion.mpr ⟨c,?_⟩⟩
  rw [mem_smul_set_iff_inv_smul_mem]
  change r • ((r⁻¹*g') • τ) ∈ ModularGroup.fd
  rw [←mul_smul,mul_inv_cancel_left]
  change g • τ ∈ ModularGroup.fd
  exact hg
end QEC.Coding.TannerLiftedProduct
