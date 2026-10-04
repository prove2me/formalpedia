-- Prove2me | solution 1 for TeschlODE.IVP.contraction_principle
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:12:39.987221+00:00
-- url     : https://prove2.me/submissions/318059bb-da65-44fb-af05-fc77246883a1

import Mathlib

set_option autoImplicit false

theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (C : Set X) (hC : IsClosed C) (hne : C.Nonempty)
    (K : X → X) (hK : Set.MapsTo K C C) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hcontr : ∀ x ∈ C, ∀ y ∈ C, ‖K x - K y‖ ≤ θ * ‖x - y‖) :
    ∃ xbar ∈ C, K xbar = xbar ∧ (∀ y ∈ C, K y = y → y = xbar) ∧
      ∀ x ∈ C, ∀ m : ℕ, ‖K^[m] x - xbar‖ ≤ θ ^ m / (1 - θ) * ‖K x - x‖ := by
  have : CompleteSpace C := hC.completeSpace_coe
  have : Nonempty C := hne.to_subtype
  let f : C → C := hK.restrict K C C
  have hfv : ∀ a : C, ((f a : C) : X) = K a := fun a => rfl
  let q : NNReal := ⟨θ, hθ0⟩
  have hq : (q : ℝ) = θ := rfl
  have hθ1' : q < 1 := by
    rw [← NNReal.coe_lt_coe, hq, NNReal.coe_one]; exact hθ1
  have hL : LipschitzWith q f := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm, hfv, hfv]
    exact hcontr a a.2 b b.2
  have hc : ContractingWith q f := ⟨hθ1', hL⟩
  let p : C := ContractingWith.fixedPoint f hc
  refine ⟨(p : X), p.2, ?_, ?_, ?_⟩
  · have h := hc.fixedPoint_isFixedPt
    have := congrArg Subtype.val h
    rw [hfv] at this
    exact this
  · intro y hy hKy
    have hfix : Function.IsFixedPt f ⟨y, hy⟩ := Subtype.ext hKy
    exact congrArg Subtype.val (hc.fixedPoint_unique hfix)
  · intro x hx m
    have h := hc.apriori_dist_iterate_fixedPoint_le ⟨x, hx⟩ m
    have hit : ∀ n : ℕ, ((f^[n] ⟨x, hx⟩ : C) : X) = K^[n] x := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hfv, ih]
    rw [Subtype.dist_eq, Subtype.dist_eq, hit, dist_eq_norm, dist_eq_norm, hfv] at h
    have e : ‖x - K x‖ = ‖K x - x‖ := norm_sub_rev _ _
    rw [e] at h
    rw [hq] at h
    calc ‖K^[m] x - (p : X)‖ ≤ ‖K x - x‖ * θ ^ m / (1 - θ) := h
      _ = θ ^ m / (1 - θ) * ‖K x - x‖ := by ring
