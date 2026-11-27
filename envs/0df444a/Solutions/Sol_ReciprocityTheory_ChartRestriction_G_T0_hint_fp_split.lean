-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hint_fp_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:54:17.338987+00:00
-- url     : https://prove2.me/submissions/13b78cc0-c787-442a-adf1-0da0964235af

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ComponentFormProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintLogFinprod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_zpow_split
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {R Fr ι : Type*} [CommRing R] [Field Fr] [Algebra R Fr] (S : Set ι)
    (g : ι → R) (e : ι → ℤ) :
    ∃ s : Finset ι, (∀ p ∈ s, p ∈ S ∧ e p ≠ 0) ∧
      ∏ᶠ (p : ι) (_ : p ∈ S), algebraMap R Fr (g p) ^ e p =
        algebraMap R Fr (∏ p ∈ s, g p ^ (e p).toNat) /
          algebraMap R Fr (∏ p ∈ s, g p ^ (-e p).toNat) := by
  classical
  by_cases hfin : (Function.mulSupport fun p => ∏ᶠ (_ : p ∈ S), algebraMap R Fr (g p) ^ e p).Finite
  · refine ⟨hfin.toFinset, fun p hp => ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset, Function.mem_mulSupport] at hp
      by_cases hpS : p ∈ S
      · exact ⟨hpS, fun h0 => hp (by simp [hpS, h0])⟩
      · exact (hp (by simp [hpS])).elim
    · rw [finprod_eq_prod _ hfin, map_prod, map_prod, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Set.Finite.mem_toFinset, Function.mem_mulSupport] at hp
      have hpS : p ∈ S := by
        by_contra h
        exact hp (by simp [h])
      rw [finprod_eq_if, if_pos hpS, map_pow, map_pow]
      exact hint_zpow_split _ _
  · refine ⟨∅, by simp, ?_⟩
    rw [finprod_of_infinite_mulSupport hfin]
    simp
end ReciprocityTheory.ChartRestriction.G.T0
