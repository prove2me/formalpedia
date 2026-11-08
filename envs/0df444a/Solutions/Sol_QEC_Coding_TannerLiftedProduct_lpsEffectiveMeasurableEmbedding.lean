-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveMeasurableEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:47:07.347091+00:00
-- url     : https://prove2.me/submissions/310ab510-c6b8-4339-8e12-8694ee515a07

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
theorem _root_.solution (g : lpsEffectiveModularGroup) :
    MeasurableEmbedding (fun τ : ℍ => g • τ) := by
  obtain ⟨h,hh⟩ := lpsEffectiveRepresentative g
  have he : (fun τ : ℍ => g • τ) = (fun τ => (h : GL (Fin 2) ℝ) • τ) := by
    funext τ
    change (g : Equiv.Perm ℍ) τ = _
    rw [hh]
    exact ModularGroup.sl_moeb h τ
  rw [he]
  exact measurableEmbedding_const_smul _
end QEC.Coding.TannerLiftedProduct
