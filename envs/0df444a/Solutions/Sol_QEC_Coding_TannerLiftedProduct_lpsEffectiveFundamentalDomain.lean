-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:22:25.568962+00:00
-- url     : https://prove2.me/submissions/48f650de-bdf5-4cc1-a070-d756b82176bc

import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Countable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFdAeFdo
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveDisjoint

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    IsFundamentalDomain lpsEffectiveModularGroup ModularGroup.fd volume := by
  apply IsFundamentalDomain.mk'' ModularGroup.isClosed_fd.measurableSet.nullMeasurableSet
  · apply Eventually.of_forall
    intro τ
    obtain ⟨h,hh⟩ := ModularGroup.exists_smul_mem_fd τ
    exact ⟨(MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict h,hh⟩
  · intro g hg
    have ha : g • ModularGroup.fd =ᵐ[volume] g • ModularGroup.fdo := by
      have := (lpsEffectiveMeasurePreserving g⁻¹).quasiMeasurePreserving.ae_eq lpsFdAeFdo
      change (fun x => x ∈ g • ModularGroup.fd) =ᵐ[volume] (fun x => x ∈ g • ModularGroup.fdo)
      filter_upwards [this] with x hx
      simp only [mem_smul_set_iff_inv_smul_mem]
      change ModularGroup.fd (g⁻¹ • x) = ModularGroup.fdo (g⁻¹ • x)
      exact hx
    exact (lpsEffectiveDisjoint g hg).aedisjoint.congr ha lpsFdAeFdo
  · intro g
    exact (lpsEffectiveMeasurePreserving g).quasiMeasurePreserving
end QEC.Coding.TannerLiftedProduct
