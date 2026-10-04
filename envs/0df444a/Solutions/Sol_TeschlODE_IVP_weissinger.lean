-- Prove2me | solution 1 for TeschlODE.IVP.weissinger
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T20:27:44.133113+00:00
-- url     : https://prove2.me/submissions/3b81a029-d2e0-450c-b369-ea4545001887

import Mathlib

set_option autoImplicit false

open Filter Topology

namespace De83b9d5

theorem limit_exists {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (C : Set X) (hC : IsClosed C)
    (K : X → X) (hK : Set.MapsTo K C C) (θ : ℕ → ℝ)
    (hθ : ∀ m : ℕ, 1 ≤ m → ∀ x ∈ C, ∀ y ∈ C, ‖K^[m] x - K^[m] y‖ ≤ θ m * ‖x - y‖)
    (hsum : Summable θ) (x : X) (hx : x ∈ C) :
    ∃ a ∈ C, K a = a ∧ ∀ m : ℕ, 1 ≤ m →
        ‖K^[m] x - a‖ ≤ (∑' j : ℕ, θ (m + j)) * ‖K x - x‖ := by
  set c : ℝ := ‖K x - x‖ with hc
  set f : ℕ → X := fun n => K^[n+1] x with hf
  have hmem : ∀ n, K^[n] x ∈ C := fun n => (hK.iterate n) hx
  have hKx : K x ∈ C := hK hx
  set d : ℕ → ℝ := fun n => θ (n+1) * c with hd
  have hstep : ∀ n, dist (f n) (f n.succ) ≤ d n := by
    intro n
    rw [dist_eq_norm]
    have h1 : f n.succ = K^[n+1] (K x) := by
      simp only [hf, Nat.succ_eq_add_one]
      rw [Function.iterate_succ_apply]
    rw [h1]
    have := hθ (n+1) (by omega) x hx (K x) hKx
    simp only [hd, hc]
    calc ‖f n - K^[n+1] (K x)‖ = ‖K^[n+1] x - K^[n+1] (K x)‖ := rfl
      _ ≤ θ (n+1) * ‖x - K x‖ := this
      _ = θ (n+1) * ‖K x - x‖ := by rw [norm_sub_rev]
  have hdsum : Summable d := by
    have : Summable (fun n => θ (n+1)) := (summable_nat_add_iff 1).mpr hsum
    exact this.mul_right c
  have hcs : CauchySeq f := cauchySeq_of_dist_le_of_summable d hstep hdsum
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcs
  have hfmem : ∀ n, f n ∈ C := fun n => hmem (n+1)
  have haC : a ∈ C := hC.mem_of_tendsto ha (Eventually.of_forall hfmem)
  refine ⟨a, haC, ?_, ?_⟩
  · -- fixed point
    have h1 : Tendsto (fun n => K (f n)) atTop (𝓝 (K a)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h0 : Tendsto (fun n => ‖f n - a‖) atTop (𝓝 0) :=
        (tendsto_iff_norm_sub_tendsto_zero).mp ha
      have h2 : Tendsto (fun n => |θ 1| * ‖f n - a‖) atTop (𝓝 0) := by
        simpa using h0.const_mul (|θ 1|)
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h2
      have := hθ 1 le_rfl (f n) (hfmem n) a haC
      simp only [Function.iterate_one] at this
      calc ‖K (f n) - K a‖ ≤ θ 1 * ‖f n - a‖ := this
        _ ≤ |θ 1| * ‖f n - a‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    have h2 : Tendsto (fun n => K (f n)) atTop (𝓝 a) := by
      have : (fun n => K (f n)) = fun n => f (n+1) := by
        funext n
        simp only [hf]
        rw [← Function.iterate_succ_apply' K (n+1) x]
      rw [this]
      exact ha.comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique h1 h2
  · intro m hm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have := dist_le_tsum_of_dist_le_of_tendsto d hstep hdsum ha n
    rw [dist_eq_norm] at this
    calc ‖K^[n+1] x - a‖ = ‖f n - a‖ := rfl
      _ ≤ ∑' j, d (n + j) := this
      _ = ∑' j, θ (n + 1 + j) * c := by
          apply tsum_congr
          intro j
          simp only [hd]
          congr 2
          omega
      _ = (∑' j : ℕ, θ (n + 1 + j)) * c := tsum_mul_right

end De83b9d5

theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (C : Set X) (hC : IsClosed C) (hne : C.Nonempty)
    (K : X → X) (hK : Set.MapsTo K C C) (θ : ℕ → ℝ)
    (hθ : ∀ m : ℕ, 1 ≤ m → ∀ x ∈ C, ∀ y ∈ C, ‖K^[m] x - K^[m] y‖ ≤ θ m * ‖x - y‖)
    (hsum : Summable θ) :
    ∃ xbar ∈ C, K xbar = xbar ∧ (∀ y ∈ C, K y = y → y = xbar) ∧
      ∀ x ∈ C, ∀ m : ℕ, 1 ≤ m →
        ‖K^[m] x - xbar‖ ≤ (∑' j : ℕ, θ (m + j)) * ‖K x - x‖ := by
  -- uniqueness of fixed points
  have huniq : ∀ y ∈ C, K y = y → ∀ z ∈ C, K z = z → y = z := by
    intro y hy hKy z hz hKz
    have ht : Tendsto θ atTop (𝓝 0) := hsum.tendsto_atTop_zero
    obtain ⟨N, hN⟩ := (eventually_atTop.mp (ht.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))))
    have hlt := hN (N+1) (by omega)
    have h := hθ (N+1) (by omega) y hy z hz
    rw [Function.iterate_fixed hKy, Function.iterate_fixed hKz] at h
    have hn : ‖y - z‖ = 0 := by
      have := norm_nonneg (y - z)
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨a, haC, hKa, -⟩ := De83b9d5.limit_exists C hC K hK θ hθ hsum x0 hx0
  refine ⟨a, haC, hKa, fun y hy hKy => huniq y hy hKy a haC hKa, ?_⟩
  intro x hx m hm
  obtain ⟨b, hbC, hKb, hb⟩ := De83b9d5.limit_exists C hC K hK θ hθ hsum x hx
  have : b = a := huniq b hbC hKb a haC hKa
  rw [← this]
  exact hb m hm
