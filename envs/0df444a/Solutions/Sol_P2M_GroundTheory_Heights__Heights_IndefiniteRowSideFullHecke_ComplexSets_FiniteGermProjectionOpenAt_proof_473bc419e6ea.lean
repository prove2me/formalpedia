-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteGermProjectionOpenAt_proof_473bc419e6ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:58:12.897663+00:00
-- url     : https://prove2.me/submissions/fee5980a-61dc-4fd0-ad9e-dc8db4ba1a53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteGermProjectionOpenAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germ_prod_eventually_zero_3a8cb7987426
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_of_projection_germ_injective_54b9f095253d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FiniteGermProjectionOpenAt
theorem _root_.solution (hcomp : AnalyticGermComponents.Statement)
    (hirr : IrreducibleFiniteGermProjectionOpenAt.Statement) : FiniteGermProjectionOpenAt.Statement := by
  classical
  intro σ _ X x d A hX hiso hinj V hV
  have hxX : x ∈ X := mem_of_projection_germ_injective A hX hinj
  obtain ⟨n, Y, hY, W, hW, hXW⟩ := hcomp σ X x hX hxX
  obtain ⟨W₀, hW₀, hisoW₀⟩ := hiso

  have hsome : ∃ i, ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) →
      (∀ᶠ z in 𝓝 x, z ∈ Y i → h (A z) = 0) → ∀ᶠ y in 𝓝 (A x), h y = 0 := by
    by_contra hnone
    push Not at hnone
    choose h han hvan hne using hnone
    have hprod : ∀ᶠ y in 𝓝 (A x), ∏ i ∈ Finset.univ, h i y = 0 := by
      have hpan : AnalyticAt ℂ (fun y => ∏ i ∈ Finset.univ, h i y) (A x) :=
        Finset.analyticAt_fun_prod Finset.univ fun i _ => han i
      refine hinj (fun y => ∏ i ∈ Finset.univ, h i y) hpan ?_
      filter_upwards [Filter.eventually_all.2 hvan, hW] with z hz hzW hzX
      have hmem : z ∈ (⋃ i, Y i) ∩ W := by
        rw [← hXW]
        exact ⟨hzX, hzW⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hmem.1
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hz i hi)
    obtain ⟨i, -, hi⟩ := germ_prod_eventually_zero h Finset.univ (fun i _ => han i) hprod
    exact hne i (hi.mono fun z hz => not_not.2 hz)
  obtain ⟨i, hi⟩ := hsome
  have hYX : Y i ∩ W ⊆ X := fun z hz => by
    have hmem : z ∈ (⋃ j, Y j) ∩ W := ⟨Set.mem_iUnion.2 ⟨i, hz.1⟩, hz.2⟩
    rw [← hXW] at hmem
    exact hmem.1
  have hisoY : ∃ W' ∈ 𝓝 x, ∀ x' ∈ Y i ∩ W', A x' = A x → x' = x :=
    ⟨W ∩ W₀, Filter.inter_mem hW hW₀, fun x' hx' hAx' => hisoW₀ x' ⟨hYX ⟨hx'.1, hx'.2.1⟩, hx'.2.2⟩ hAx'⟩
  have himg := hirr σ (Y i) x d A (hY i).1 (hY i).2 hisoY hi (V ∩ W) (Filter.inter_mem hV hW)
  refine Filter.mem_of_superset himg (Set.image_mono ?_)
  rintro z ⟨hzY, hzV, hzW⟩
  exact ⟨hYX ⟨hzY, hzW⟩, hzV⟩
end FiniteGermProjectionOpenAt
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
