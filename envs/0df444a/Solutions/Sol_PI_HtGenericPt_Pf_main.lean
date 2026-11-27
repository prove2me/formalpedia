-- Prove2me | solution 1 for PI.HtGenericPt.Pf.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:14:26.926559+00:00
-- url     : https://prove2.me/submissions/82176184-4fa2-44f3-b439-93d3b660f5dc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GenericPointHeight_GenericPointStatements_GenericPointLemmas_GenericPointWeights_Wx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.HtGenericPt PI.HtGenericPt.Pf
namespace PI.HtGenericPt.Pf
theorem _root_.solution {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT] {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A) : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.exists_generic 𝒜 d := by
  unfold ReciprocityTheory.ChartRestriction.G.T0.LeafSt.exists_generic
  intro hd h
  refine ⟨?_, ?_⟩
  · haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
    have hL : ∀ (c : ι) (x : Fin (d.N + 1) → K),
        ((LinearMap.proj c : ((c : ι) → A c) →ₗ[K] A c) ∘ₗ
          (∑ j, (LinearMap.proj j : (Fin (d.N + 1) → K) →ₗ[K] K).smulRight (d.w j))) x = d.wx x c := by
      intro c x
      simp [ReciprocityTheory.ChartRestriction.G.T0.Data.wx, LinearMap.sum_apply, Finset.sum_apply]
    have hne : ∀ c, LinearMap.ker ((LinearMap.proj c : ((c : ι) → A c) →ₗ[K] A c) ∘ₗ
        (∑ j, (LinearMap.proj j : (Fin (d.N + 1) → K) →ₗ[K] K).smulRight (d.w j))) ≠ ⊤ := by
      intro c htop
      have hmem : (Pi.single (d.jc c) 1 : Fin (d.N + 1) → K) ∈
          LinearMap.ker ((LinearMap.proj c : ((c : ι) → A c) →ₗ[K] A c) ∘ₗ
            (∑ j, (LinearMap.proj j : (Fin (d.N + 1) → K) →ₗ[K] K).smulRight (d.w j))) := by
        rw [htop]
        exact Submodule.mem_top
      rw [LinearMap.mem_ker, hL] at hmem
      apply hd.w_base c
      simpa [ReciprocityTheory.ChartRestriction.G.T0.Data.wx, Pi.single_apply, Finset.sum_apply, ite_apply, Pi.zero_apply,
        Finset.sum_ite_eq'] using hmem
    obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top _ hne
    refine ⟨x, fun c => ?_⟩
    have hxc := hx c
    rw [LinearMap.mem_ker, hL] at hxc
    exact hxc
  · obtain ⟨e, he, -⟩ := hd.a4
    exact ⟨e, he⟩
end PI.HtGenericPt.Pf
