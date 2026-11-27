-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.eq_of_point_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:24:37.110335+00:00
-- url     : https://prove2.me/submissions/41772feb-23b9-4b4d-bd3f-033abdd50af7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chartIdeal_ne_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isUnit_mk_chartIdeal_form

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
variable {W : Ideal (MRingOver F ι)}
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution {P : Ideal (MRingOver F ι)} (hW : IsProjVarF W 0) (hP : P.IsPrime)
    (hPh : IsMultiHomogIdeal P) {j : ∀ k, ι k} (hj : IsChart P j) (hWP : W ≤ P) : P = W := by
  classical
  refine le_antisymm ?_ hWP
  intro x hxP
  by_contra hxW
  obtain ⟨S, hS, hPS⟩ := hPh
  have hex : ∃ s ∈ S, s ∉ W := by
    by_contra! h
    exact hxW ((hPS ▸ Ideal.span_le.mpr h : P ≤ W) hxP)
  obtain ⟨s, hsS, hsW⟩ := hex
  obtain ⟨a, ha⟩ := hS s hsS
  have hsP : s ∈ P := hPS ▸ Ideal.subset_span hsS
  obtain ⟨t, ht⟩ := (isUnit_mk_chartIdeal_form hW j ha hsW).exists_right_inv
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
  have h1 : s * t - 1 ∈ chartIdeal W j := by
    rw [← Ideal.Quotient.eq, map_mul, ht, map_one]
  have h2 : chartIdeal W j ≤ chartIdeal P j := sup_le_sup_right hWP _
  have h3 : s * t ∈ chartIdeal P j := Ideal.mem_sup_left (P.mul_mem_right t hsP)
  have h4 : (1 : MRingOver F ι) ∈ chartIdeal P j := by
    have := Ideal.sub_mem _ h3 (h2 h1)
    simpa using this
  haveI := hP
  exact chartIdeal_ne_top (W := P) ⟨S, hS, hPS⟩ hj ((Ideal.eq_top_iff_one _).mpr h4)
end ReciprocityTheory.ChartRestriction.G.AI.I1
