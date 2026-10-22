-- Prove2me | solution 1 for ReinfRegGames.StrictStable.proposition_C_3_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:32:51.138224+00:00
-- url     : https://prove2.me/submissions/e813342e-844b-4f84-90eb-f1a132b1d14f

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
set_option autoImplicit false

open Filter Topology

theorem solution {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : ReinfRegGames.Extinction.IsPenalty h K)
    (p : B → ℝ) (hp : p ∈ stdSimplex ℝ B) (y x : B → ℝ) (hx : ReinfRegGames.Extinction.IsChoice h y x) :
    1 / 2 * K * ReinfRegGames.Extinction.sqDist x p ≤ ReinfRegGames.Extinction.fenchelCoupling h p y := by
  obtain ⟨_, _, hK, hconv⟩ := hpen
  obtain ⟨hxs, hmax⟩ := hx
  have hconj : ReinfRegGames.Extinction.conj h y = y ⬝ᵥ x - h x := by
    unfold ReinfRegGames.Extinction.conj
    apply IsGreatest.csSup_eq
    constructor
    · exact ⟨x, hxs, rfl⟩
    · rintro _ ⟨x', hx', rfl⟩
      exact hmax x' hx'
  unfold ReinfRegGames.Extinction.fenchelCoupling
  rw [hconj]
  set d := ReinfRegGames.Extinction.sqDist x p with hd
  have hd' : ReinfRegGames.Extinction.sqDist p x = d := by
    simp only [hd, ReinfRegGames.Extinction.sqDist]
    apply Finset.sum_congr rfl; intro i _; ring
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      1 / 2 * K * (1 - t) * d ≤ h p + (y ⬝ᵥ x - h x) - y ⬝ᵥ p := by
    intro t ht0 ht1
    have hmem : t • p + (1 - t) • x ∈ stdSimplex ℝ B :=
      (convex_stdSimplex ℝ B) hp hxs ht0.le (by linarith) (by ring)
    have h1 := hconv p hp x hxs t ⟨ht0.le, ht1⟩
    rw [hd'] at h1
    have h2 := hmax _ hmem
    have h3 : y ⬝ᵥ (t • p + (1 - t) • x) = t * (y ⬝ᵥ p) + (1 - t) * (y ⬝ᵥ x) := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul]; simp
    rw [h3] at h2
    -- h2 : t*(y.p) + (1-t)*(y.x) - h(xt) ≤ y.x - h x
    have h4 : t * (y ⬝ᵥ p - y ⬝ᵥ x) ≤ h (t • p + (1 - t) • x) - h x := by linarith
    have h5 : t * (y ⬝ᵥ p - y ⬝ᵥ x) ≤ t * (h p - h x) - 1 / 2 * K * t * (1 - t) * d := by linarith
    have h6 : t * (1 / 2 * K * (1 - t) * d) ≤ t * (h p + (y ⬝ᵥ x - h x) - y ⬝ᵥ p) := by nlinarith
    exact le_of_mul_le_mul_left h6 ht0
  have hlim : Tendsto (fun t : ℝ => 1 / 2 * K * (1 - t) * d) (𝓝[>] 0) (𝓝 (1 / 2 * K * (1 - 0) * d)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : Continuous (fun t : ℝ => 1 / 2 * K * (1 - t) * d) := by fun_prop
    exact hc.tendsto 0
  have := le_of_tendsto hlim (Filter.eventually_of_mem (Ioo_mem_nhdsGT (zero_lt_one' ℝ))
    (fun t ht => key t ht.1 ht.2.le))
  simpa using this
