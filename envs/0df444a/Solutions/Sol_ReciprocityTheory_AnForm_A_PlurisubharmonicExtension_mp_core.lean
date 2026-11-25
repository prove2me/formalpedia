-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.mp_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:40.223676+00:00
-- url     : https://prove2.me/submissions/a27ccc20-ec03-4734-bcf4-e6be403abc88

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution {k : ℂ → ℝ} {c ζ0 : ℂ} {r η : ℝ} {E : Finset ℂ}
    (hζ0 : ζ0 ∈ closedBall c r) (hζ0E : ζ0 ∉ E) (hη : 0 < η)
    (hcont : ContinuousOn k (closedBall c r \ ↑E))
    (hsph : ∀ ζ ∈ sphere c r, k ζ < k ζ0)
    (hpunct : ∀ e ∈ E, ∀ ζ ∈ closedBall c r \ ↑E, 0 < dist ζ e → dist ζ e < η → k ζ < k ζ0)
    (hsub : ∀ a s, 0 < s → closedBall a s ⊆ ball c r \ ↑E → k a < circleAverage k a s) :
    False := by
  set K := closedBall c r \ ⋃ e ∈ E, ball e (η / 2) with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall c r).diff (isOpen_biUnion fun e _ => isOpen_ball)
  have hKE : K ⊆ closedBall c r \ ↑E := by
    intro x hx
    refine ⟨hx.1, fun hxE => hx.2 ?_⟩
    exact Set.mem_biUnion hxE (mem_ball_self (by linarith))
  have hζ0K : ζ0 ∈ K := by
    refine ⟨hζ0, ?_⟩
    simp only [Set.mem_iUnion, mem_ball, not_exists]
    intro e he hd
    have hpos : 0 < dist ζ0 e := dist_pos.2 (fun h => hζ0E (h ▸ he))
    exact lt_irrefl _ (hpunct e he ζ0 ⟨hζ0, hζ0E⟩ hpos (by linarith))
  obtain ⟨ζ1, hζ1K, hmax⟩ := hKc.exists_isMaxOn ⟨ζ0, hζ0K⟩ (hcont.mono hKE)
  have h10 : k ζ0 ≤ k ζ1 := hmax hζ0K
  have hin : dist ζ1 c < r := by
    rcases (mem_closedBall.1 hζ1K.1).lt_or_eq with h | h
    · exact h
    · exact absurd (hsph ζ1 (mem_sphere.2 h)) (not_lt.2 h10)
  have hfar : ∀ e ∈ E, η ≤ dist ζ1 e := by
    intro e he
    by_contra hlt
    push Not at hlt
    have h2 : η / 2 ≤ dist ζ1 e := by
      by_contra h3
      push Not at h3
      exact hζ1K.2 (Set.mem_biUnion he (mem_ball.2 h3))
    exact absurd (hpunct e he ζ1 (hKE hζ1K) (by linarith) hlt) (not_lt.2 h10)
  set s := min (r - dist ζ1 c) (η / 2) / 2 with hs
  have hm0 : 0 < min (r - dist ζ1 c) (η / 2) := lt_min (by linarith) (by linarith)
  have hs0 : 0 < s := by rw [hs]; linarith
  have hs1 : s ≤ (r - dist ζ1 c) / 2 := by
    have := min_le_left (r - dist ζ1 c) (η / 2); rw [hs]; linarith
  have hs2 : s ≤ η / 4 := by
    have := min_le_right (r - dist ζ1 c) (η / 2); rw [hs]; linarith
  have hsK : closedBall ζ1 s ⊆ K := by
    intro x hx
    have hx' := mem_closedBall.1 hx
    refine ⟨mem_closedBall.2 ?_, ?_⟩
    · linarith [dist_triangle x ζ1 c]
    · simp only [Set.mem_iUnion, mem_ball, not_exists, not_lt]
      intro e he
      have h1 := hfar e he
      have h2 := dist_triangle ζ1 x e
      rw [dist_comm ζ1 x] at h2
      linarith
  have hsB : closedBall ζ1 s ⊆ ball c r \ ↑E := by
    intro x hx
    refine ⟨mem_ball.2 ?_, (hKE (hsK hx)).2⟩
    have hx' := mem_closedBall.1 hx
    linarith [dist_triangle x ζ1 c]
  have hlt := hsub ζ1 s hs0 hsB
  have hle : circleAverage k ζ1 s ≤ k ζ1 := by
    apply circleAverage_mono_on_of_le_circle
    · apply ContinuousOn.circleIntegrable hs0.le
      exact (hcont.mono hKE).mono (sphere_subset_closedBall.trans hsK)
    · intro x hx
      rw [abs_of_pos hs0] at hx
      exact hmax (hsK (sphere_subset_closedBall hx))
  linarith
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
