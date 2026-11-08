-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:20:11.059149+00:00
-- url     : https://prove2.me/submissions/2024f4ef-6797-4ee9-9532-5e53fce3ccc1

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
theorem _root_.solution (g : lpsEffectiveModularGroup) (hg : g ≠ 1) :
    Disjoint (g • ModularGroup.fdo) ModularGroup.fdo := by
  obtain ⟨h,hh⟩ := lpsEffectiveRepresentative g
  apply Set.disjoint_left.mpr
  rintro τ ⟨z,hz,rfl⟩ hτ
  have hτ' : h • z ∈ ModularGroup.fdo := by
    change (g : Equiv.Perm ℍ) z ∈ ModularGroup.fdo at hτ
    simpa only [hh, MulAction.toPerm_apply] using hτ
  have he : (g : Equiv.Perm ℍ) = 1 := by
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo hz hτ' with rfl | rfl
    · rw [hh]
      ext z
      simp
    · rw [hh]
      ext z
      simp [-ModularGroup.sl_moeb]
  exact hg (Subtype.ext he)
end QEC.Coding.TannerLiftedProduct
