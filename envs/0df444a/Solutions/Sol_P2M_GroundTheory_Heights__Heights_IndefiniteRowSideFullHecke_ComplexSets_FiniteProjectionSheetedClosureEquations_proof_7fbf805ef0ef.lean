-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteProjectionSheetedClosureEquations_proof_7fbf805ef0ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:58:22.143292+00:00
-- url     : https://prove2.me/submissions/acd48e19-d8a5-41fb-83be-37a82d3e9d68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionSheetedClosureEquations
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionProperBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperSheetedFibreEsymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGridProductLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionSheetedClosureEquations
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteProjectionSheetedClosureEquations_surjective_of_no_germ_627f9b1e5c93
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteProjectionSheetedClosureEquations_prod_sub_eq_sum_esymm_b2bed9e083b1

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
open Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FiniteProjectionSheetedClosureEquations
theorem _root_.solution
    (hball : FiniteProjectionProperBall.Statement)
    (hcount : UnbranchedProperCountConstant.Statement)
    (hesymm : ProperSheetedFibreEsymm.Statement)
    (hgrid : GridProductLowerBound.Statement) :
    FiniteProjectionSheetedClosureEquations.Statement := by
  intro σ _ X w d A hX hiso hA δ hδ hsh
  classical
  have hsurj := FiniteProjectionSheetedClosureEquations.surjective_of_no_germ A hA
  by_cases hz : ∀ᶠ t in 𝓝 (A w), δ t = 0
  · have hz' : ∀ᶠ z in 𝓝 w, δ (A z) = 0 := (A.continuous.tendsto w).eventually hz
    refine ⟨1, fun _ _ => 1, fun _ => analyticAt_const, ?_,
      Eventually.of_forall fun z _ h => absurd (h 0) one_ne_zero⟩
    filter_upwards [hz'] with z hz0 _ hne
    exact absurd hz0 hne
  obtain ⟨M, hM, hMsh⟩ := hsh
  obtain ⟨ρ, hρ, r, hr, hρM, hK⟩ := hball σ X w d A hX hiso M hM
  obtain ⟨r₂, hr₂, hδr⟩ := Metric.eventually_nhds_iff_ball.1 hδ.eventually_analyticAt
  set D : Set (Fin d → ℂ) := Metric.ball (A w) (min r r₂) with hDdef
  set Y : Set (σ → ℂ) := {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ D} with hYdef
  have hDo : IsOpen D := Metric.isOpen_ball
  have hDc : IsPreconnected D := (convex_ball _ _).isPreconnected
  have hwD : A w ∈ D := Metric.mem_ball_self (lt_min hr hr₂)
  have hmap : Set.MapsTo A Y D := fun x hx => hx.2
  have hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K} := by
    intro K hKD hKc
    have hKr : K ⊆ Metric.ball (A w) r := hKD.trans (Metric.ball_subset_ball (min_le_left _ _))
    have heq : {x | x ∈ Y ∧ A x ∈ K} = {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ K} := by
      ext x
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hKD h.2⟩, h.2⟩⟩
    rw [heq]
    exact hK K hKr hKc
  have hδD : AnalyticOnNhd ℂ δ D := fun t ht => hδr t (Metric.ball_subset_ball (min_le_right _ _) ht)
  have hne : ∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ D → W.Nonempty → ∃ t ∈ W, δ t ≠ 0 := by
    rintro W hWo hWD ⟨t, ht⟩
    by_contra hall
    push Not at hall
    have hev : δ =ᶠ[𝓝 t] 0 := by
      filter_upwards [hWo.mem_nhds ht] with s hs
      exact hall s hs
    have h0 := hδD.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc (hWD ht) hev
    apply hz
    filter_upwards [hDo.mem_nhds hwD] with s hs
    exact h0 hs
  have hsec : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O := by
    intro x hx hδx
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hMsh x ⟨hx.1.1, hρM hx.1.2⟩ hδx
    refine ⟨O ∩ g ⁻¹' Metric.ball w ρ ∩ D, V ∩ Metric.ball w ρ ∩ A ⁻¹' D, g,
      (hg.continuousOn.isOpen_inter_preimage hO Metric.isOpen_ball).inter hDo,
      (hV.inter Metric.isOpen_ball).inter (hDo.preimage A.continuous), ⟨⟨hxV, hx.1.2⟩, hx.2⟩,
      hg.mono fun t ht => ht.1.1, fun y hy => hAg y hy.1.1, ?_⟩
    ext z
    constructor
    · rintro ⟨⟨⟨hzX, hzb⟩, hzD⟩, ⟨⟨hzV, -⟩, -⟩⟩
      have hzg : z ∈ g '' O := by
        rw [← hXV]
        exact ⟨hzX, hzV⟩
      obtain ⟨t, ht, rfl⟩ := hzg
      refine ⟨t, ⟨⟨ht, hzb⟩, ?_⟩, rfl⟩
      rw [hAg t ht] at hzD
      exact hzD
    · rintro ⟨t, ⟨⟨ht, htb⟩, htD⟩, rfl⟩
      have hmem : g t ∈ X ∩ V := by
        rw [hXV]
        exact ⟨t, ht, rfl⟩
      have hA' : A (g t) ∈ D := by
        rw [hAg t ht]
        exact htD
      exact ⟨⟨⟨hmem.1, htb⟩, hA'⟩, ⟨⟨hmem.2, htb⟩, hA'⟩⟩
  obtain ⟨N, hN⟩ := hcount σ Y d A D δ hDo hDc hmap hprop hδD fun x hx hx' => by
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ := hsec x hx hx'
    exact ⟨O, V, g, hO, hV, hxV, hg.continuousOn, hAg, hYV⟩
  let l : (σ → Fin (N + 1)) → (σ → ℂ) →L[ℂ] ℂ := fun u =>
    ∑ i, ((u i : ℕ) : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i
  have hl : ∀ u z, l u z = ∑ i, ((u i : ℕ) : ℂ) * z i := by
    intro u z
    simp [l]
  choose F hFan hFeq using fun u j => hesymm σ Y d A D δ (l u) j hDo hmap hprop hδD hne hsec
  let c : (σ → Fin (N + 1)) → (σ → ℂ) → ℂ := fun u z =>
    ∑ j ∈ Finset.range (N + 1), (-1) ^ j * F u j (A z) * l u z ^ (N - j)
  have hfib : ∀ z, A z ∈ D → δ (A z) ≠ 0 → ∃ s : Finset (σ → ℂ),
      (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = A z} ∧ s.card = N := by
    intro z hzD hδz
    have h := hN (A z) hzD hδz
    have hfin := Set.finite_of_encard_eq_coe h
    refine ⟨hfin.toFinset, hfin.coe_toFinset, ?_⟩
    have h' : ((hfin.toFinset : Finset (σ → ℂ)) : Set (σ → ℂ)).encard = N := by
      rw [hfin.coe_toFinset]
      exact h
    rw [Set.encard_coe_eq_coe_finsetCard] at h'
    exact_mod_cast h'
  have hprod : ∀ u z, A z ∈ D → δ (A z) ≠ 0 → ∀ s : Finset (σ → ℂ),
      (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = A z} → s.card = N →
      c u z = ∏ x ∈ s, (l u z - l u x) := by
    intro u z hzD hδz s hs hcard
    have hm : Multiset.card (s.val.map (l u)) = N := by simp [hcard]
    have key := FiniteProjectionSheetedClosureEquations.prod_sub_eq_sum_esymm (s.val.map (l u)) (l u z)
    rw [hm, Multiset.map_map] at key
    rw [Finset.prod_eq_multiset_prod]
    refine Eq.trans ?_ key.symm
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hFeq u j (A z) hzD hδz s hs]
  have hcan : ∀ u z, A z ∈ D → AnalyticAt ℂ (c u) z := by
    intro u z hzD
    refine Finset.analyticAt_fun_sum (𝕜 := ℂ)
      (f := fun j z => (-1 : ℂ) ^ j * F u j (A z) * l u z ^ (N - j)) _ fun j _ => ?_
    have h1 : AnalyticAt ℂ (F u j ∘ A) z := (hFan u j (A z) hzD).comp (ContinuousLinearMap.analyticAt A z)
    have h2 : AnalyticAt ℂ (fun z => l u z ^ (N - j)) z := ((l u).analyticAt z).pow _
    have h0 : AnalyticAt ℂ (fun _ : σ → ℂ => ((-1 : ℂ) ^ j)) z := analyticAt_const
    exact (h0.mul h1).mul h2
  let e := (Fintype.equivFin (σ → Fin (N + 1))).symm
  have hBw : Metric.ball w ρ ∩ A ⁻¹' D ∈ 𝓝 w :=
    (Metric.isOpen_ball.inter (hDo.preimage A.continuous)).mem_nhds ⟨Metric.mem_ball_self hρ, hwD⟩
  refine ⟨Fintype.card (σ → Fin (N + 1)), fun k => c (e k), fun k => hcan _ w hwD, ?_, ?_⟩
  · filter_upwards [hBw] with z hz hzX hδz k
    obtain ⟨s, hs, hcard⟩ := hfib z hz.2 hδz
    rw [hprod _ z hz.2 hδz s hs hcard]
    have hzs : z ∈ (↑s : Set (σ → ℂ)) := by
      rw [hs]
      exact ⟨⟨⟨hzX, hz.1⟩, hz.2⟩, rfl⟩
    exact Finset.prod_eq_zero hzs (sub_self _)
  · filter_upwards [hBw] with z₀ hz₀ hz₀X hall
    by_contra hcl
    set Z : Set (σ → ℂ) := {x | x ∈ Y ∧ δ (A x) ≠ 0} with hZdef
    have hZb : Bornology.IsBounded Z := Metric.isBounded_ball.subset fun x hx => hx.1.1.2
    have hZsub : Z ⊆ {x | x ∈ X ∧ δ (A x) ≠ 0} := fun x hx => ⟨hx.1.1.1, hx.2⟩
    have hZcl : z₀ ∉ closure Z := fun h => hcl (closure_mono hZsub h)
    obtain ⟨μ, hμ, U, hU, hbound⟩ := hgrid σ N Z z₀ hZb hZcl
    have hsmall : ∀ᶠ z in 𝓝 z₀, ∀ u, ‖c u z‖ < μ := by
      rw [Filter.eventually_all]
      intro u
      have h0 : c u z₀ = 0 := by
        have := hall (e.symm u)
        simpa only [Equiv.apply_symm_apply] using this
      have hcont : Tendsto (fun x => ‖c u x‖) (𝓝 z₀) (𝓝 ‖c u z₀‖) :=
        (hcan u z₀ hz₀.2).continuousAt.norm.tendsto
      rw [h0, norm_zero] at hcont
      exact hcont.eventually (gt_mem_nhds hμ)
    obtain ⟨W, hWsub, hWo, hz₀W⟩ :=
      mem_nhds_iff.1 (inter_mem (inter_mem hU hsmall) ((hDo.preimage A.continuous).mem_nhds hz₀.2))
    obtain ⟨t, ⟨z, hzW, rfl⟩, hδt⟩ := hne (A '' W) (A.isOpenMap hsurj W hWo)
      (by rintro t ⟨z, hz, rfl⟩; exact (hWsub hz).2) ⟨A z₀, z₀, hz₀W, rfl⟩
    obtain ⟨⟨hzU, hzc⟩, hzD⟩ := hWsub hzW
    obtain ⟨s, hs, hcard⟩ := hfib z hzD hδt
    have hsZ : (↑s : Set (σ → ℂ)) ⊆ Z := by
      rw [hs]
      rintro x ⟨hxY, hxA⟩
      exact ⟨hxY, by rw [hxA]; exact hδt⟩
    obtain ⟨u, hu⟩ := hbound z hzU s hsZ hcard.le
    have hlt := hzc u
    rw [hprod u z hzD hδt s hs hcard] at hlt
    have heq : ∏ x ∈ s, (l u z - l u x) = ∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i) := by
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [hl, hl, ← Finset.sum_sub_distrib]
      simp [mul_sub]
    rw [heq] at hlt
    linarith
end FiniteProjectionSheetedClosureEquations
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
