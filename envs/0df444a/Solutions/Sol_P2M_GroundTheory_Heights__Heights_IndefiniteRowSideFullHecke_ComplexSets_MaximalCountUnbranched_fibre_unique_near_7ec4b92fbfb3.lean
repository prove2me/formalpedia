-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_MaximalCountUnbranched_fibre_unique_near_7ec4b92fbfb3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:00.553001+00:00
-- url     : https://prove2.me/submissions/10cc2501-cc34-4629-b3b0-bb2569c4d7b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaximalCountUnbranched
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaximalCountUnbranched

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
open Topology Filter Metric
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.MaximalCountUnbranched
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.MaximalCountUnbranched
theorem _root_.solution {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {N : ℕ} (hmaps : Set.MapsTo A Y D)
    (hopen : ∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x))
    (hle : ∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N)
    {z : σ → ℂ} (hz : z ∈ Y) (hzN : {x' | x' ∈ Y ∧ A x' = A z}.encard = N) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ W ∈ 𝓝 (A z), ∀ y ∈ W,
      {x' | x' ∈ Y ∧ A x' = y}.encard = N ∧ (∃ x' ∈ Y, A x' = y ∧ dist x' z < ε) ∧
      ∀ x₁ ∈ Y, ∀ x₂ ∈ Y, A x₁ = y → A x₂ = y → dist x₁ z < ε → dist x₂ z < ε → x₁ = x₂ := by
  have hSfin : {x' | x' ∈ Y ∧ A x' = A z}.Finite := Set.finite_of_encard_eq_coe hzN
  have hzS : z ∈ {x' | x' ∈ Y ∧ A x' = A z} := ⟨hz, rfl⟩
  have hsep : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ {x' | x' ∈ Y ∧ A x' = A z} ×ˢ {x' | x' ∈ Y ∧ A x' = A z},
      p.1 ≠ p.2 → 2 * ε < dist p.1 p.2 := by
    refine (eventually_all_finite (hSfin.prod hSfin)).2 fun p _ => ?_
    by_cases hp : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hp h
    · have hpos : 0 < dist p.1 p.2 / 2 := half_pos (dist_pos.2 hp)
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hpos)] with ε hε _
      linarith
  filter_upwards [hsep, self_mem_nhdsWithin] with ε hε hε0
  have hε0 : (0 : ℝ) < ε := hε0
  refine ⟨⋂ s ∈ {x' | x' ∈ Y ∧ A x' = A z}, A '' (Y ∩ ball s ε), (biInter_mem hSfin).2 fun s hs => ?_,
    fun y hy => ?_⟩
  · have := hopen s hs.1 (ball s ε) (ball_mem_nhds s hε0)
    rwa [hs.2] at this
  have hch : ∀ s ∈ {x' | x' ∈ Y ∧ A x' = A z}, ∃ p, p ∈ Y ∧ dist p s < ε ∧ A p = y := by
    intro s hs
    obtain ⟨p, ⟨hpY, hpb⟩, hpA⟩ := Set.mem_iInter₂.1 hy s hs
    exact ⟨p, hpY, mem_ball.1 hpb, hpA⟩
  choose! f hfY hfd hfA using hch
  have hinj : Set.InjOn f {x' | x' ∈ Y ∧ A x' = A z} := by
    intro s hs s' hs' he
    by_contra hne
    have h1 : 2 * ε < dist s s' := hε (s, s') ⟨hs, hs'⟩ hne
    have h2 : dist s s' ≤ dist (f s) s + dist (f s') s' := by
      calc dist s s' ≤ dist s (f s) + dist (f s) s' := dist_triangle _ _ _
        _ = dist (f s) s + dist (f s') s' := by rw [dist_comm s, he]
    linarith [hfd s hs, hfd s' hs']
  have hyD : y ∈ D := hfA z hzS ▸ hmaps (hfY z hzS)
  have hsub : f '' {x' | x' ∈ Y ∧ A x' = A z} ⊆ {x' | x' ∈ Y ∧ A x' = y} := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hfY s hs, hfA s hs⟩
  have himg : (f '' {x' | x' ∈ Y ∧ A x' = A z}).encard = N := by rw [hinj.encard_image, hzN]
  have hFle := hle y hyD
  have hFeq : {x' | x' ∈ Y ∧ A x' = y}.encard = N :=
    le_antisymm hFle (himg ▸ Set.encard_le_encard hsub)
  have huniq : ∀ x₁ ∈ Y, A x₁ = y → dist x₁ z < ε → x₁ = f z := by
    intro x₁ hx₁ hA₁ hd₁
    by_contra hne
    have hnot : x₁ ∉ f '' {x' | x' ∈ Y ∧ A x' = A z} := by
      rintro ⟨s, hs, rfl⟩
      by_cases hsz : s = z
      · exact hne (hsz ▸ rfl)
      · have h1 : 2 * ε < dist s z := hε (s, z) ⟨hs, hzS⟩ hsz
        have h2 : dist s z ≤ dist (f s) s + dist (f s) z := by
          calc dist s z ≤ dist s (f s) + dist (f s) z := dist_triangle _ _ _
            _ = dist (f s) s + dist (f s) z := by rw [dist_comm s]
        linarith [hfd s hs]
    have hins : insert x₁ (f '' {x' | x' ∈ Y ∧ A x' = A z}) ⊆ {x' | x' ∈ Y ∧ A x' = y} :=
      Set.insert_subset ⟨hx₁, hA₁⟩ hsub
    have hc := Set.encard_le_encard hins
    rw [Set.encard_insert_of_notMem hnot, himg] at hc
    have hc' : ((N + 1 : ℕ) : ℕ∞) ≤ (N : ℕ∞) := by exact_mod_cast hc.trans hFle
    have : N + 1 ≤ N := by exact_mod_cast hc'
    omega
  refine ⟨hFeq, ⟨f z, hfY z hzS, hfA z hzS, hfd z hzS⟩, fun x₁ hx₁ x₂ hx₂ hA₁ hA₂ hd₁ hd₂ => ?_⟩
  rw [huniq x₁ hx₁ hA₁ hd₁, huniq x₂ hx₂ hA₂ hd₂]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.MaximalCountUnbranched
