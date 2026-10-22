-- Prove2me | solution 1 for TwoEchelonCVRP.Config.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:41:16.972067+00:00
-- url     : https://prove2.me/submissions/3c0ab241-6d67-4104-8e1f-ae7ce914329f

import Mathlib
import Definitions.Def_TwoEchelonCVRP_Config_Configuration

set_option autoImplicit false

open TwoEchelonCVRP.Config

theorem solution (I : Instance) (RS : RouteSystem I) (M : Finset RS.FR) (hMP : InP RS M)
    (θ : Fin I.ns → ℝ)
    (hθ : ∀ t : SolFM RS, IsFeasibleFM RS M t → ∀ k ∈ NS RS M, θ k ≤ ∑ r ∈ Mk RS M k, t.qd r k)
    (htest : (I.m2 : ℤ) < ∑ k ∈ NS RS M, ⌈θ k / (I.Q2 : ℝ)⌉ ∨
      ∃ k ∈ NS RS M, (I.m k : ℤ) < ⌈θ k / (I.Q2 : ℝ)⌉) :
    ∀ t : SolFM RS, ¬ IsFeasibleFM RS M t := by
  intro t ht
  have hθt := hθ t ht
  obtain ⟨_, _, hmk, hm2, _, hflow, _, _⟩ := ht
  have hQ : (0 : ℝ) < I.Q2 := by exact_mod_cast I.Q2_pos
  have key : ∀ k ∈ NS RS M,
      ⌈θ k / (I.Q2 : ℝ)⌉ ≤
        ((∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), (t.x l).toNat : ℕ) : ℤ) := by
    intro k hk
    rw [Int.ceil_le, div_le_iff₀ hQ]
    have h1 := hθt k hk
    rw [hflow k hk] at h1
    refine h1.trans ?_
    have hsum : ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k),
        ((RS.w l * (t.x l).toNat : ℕ) : ℝ) ≤
        (I.Q2 : ℝ) * ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), ((t.x l).toNat : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro l _
      push_cast
      have h2 : (RS.w l : ℝ) ≤ I.Q2 := by exact_mod_cast RS.cap2 l
      have h0 : (0 : ℝ) ≤ ((t.x l).toNat : ℝ) := Nat.cast_nonneg _
      nlinarith
    refine hsum.trans (le_of_eq ?_)
    push_cast
    ring
  have hfib : ∑ k ∈ NS RS M, ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), (t.x l).toNat
      = ∑ l ∈ Finset.univ.filter (fun l => RS.sat l ∈ NS RS M), (t.x l).toNat := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ.filter (fun l => RS.sat l ∈ NS RS M)) (t := NS RS M) (g := RS.sat)
      (fun l hl => (Finset.mem_filter.1 hl).2)]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ hk, h⟩
    · intro h; exact h.2
  rcases htest with h | ⟨k, hk, h⟩
  · have h2 : ∑ k ∈ NS RS M, ⌈θ k / (I.Q2 : ℝ)⌉ ≤
        ((∑ l ∈ Finset.univ.filter (fun l => RS.sat l ∈ NS RS M), (t.x l).toNat : ℕ) : ℤ) := by
      rw [← hfib, Nat.cast_sum]
      exact Finset.sum_le_sum key
    omega
  · have h1 := key k hk
    have h2 := hmk k hk
    omega
