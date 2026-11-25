-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Yhc2_le_span_singleton_of_forall_mem_eq__73902d423e3a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:25.365693+00:00
-- url     : https://prove2.me/submissions/526e5b80-1d7d-4951-8541-23d2614640d9

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Yhc2.le_span_singleton_of_forall_mem_eq
theorem _root_.solution.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] {π ξ : R} [IsAdicComplete (Ideal.span {π}) R] {J : Ideal R},
      (∀ x ∈ J, ∃ (a : R), ∃ z ∈ J, x = a * ξ + z * π) → J ≤ Ideal.span {ξ} := by
  intro R _ π ξ hc J h x hx
  choose! a z hz he using h
  have hsm : ∀ (n : ℕ) (u v : R),
      u ≡ v [SMOD ((Ideal.span {π}) ^ n • ⊤ : Submodule R R)] ↔ π ^ n ∣ u - v := by
    intro n u v
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
      Ideal.mem_span_singleton]
  have hzs : ∀ n : ℕ, z^[n] x ∈ J := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => rw [Function.iterate_succ_apply']; exact hz _ ih
  let f : ℕ → R := fun n => ∑ i ∈ Finset.range n, a (z^[i] x) * π ^ i
  have hf : ∀ n, f (n + 1) = f n + a (z^[n] x) * π ^ n := fun n => Finset.sum_range_succ _ _
  have key : ∀ n, x = f n * ξ + z^[n] x * π ^ n := by
    intro n
    induction n with
    | zero => simp [f]
    | succ n ih =>
      rw [Function.iterate_succ_apply', hf]
      have h1 := he _ (hzs n)
      linear_combination ih + π ^ n * h1
  have hcau : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD ((Ideal.span {π}) ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    rw [hsm]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hf, ← sub_sub]
      exact dvd_sub ih (Dvd.dvd.mul_left (pow_dvd_pow π hmn) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete hcau
  have h0 : x - L * ξ = 0 := by
    apply IsHausdorff.haus hc.toIsHausdorff
    intro n
    rw [hsm]
    obtain ⟨c, hc'⟩ := (hsm _ _ _).1 (hL n)
    exact ⟨c * ξ + z^[n] x, by linear_combination key n + ξ * hc'⟩
  exact Ideal.mem_span_singleton'.2 ⟨L, (sub_eq_zero.1 h0).symm⟩
end UpperTheory.Reformulated.B.Yhc2.le_span_singleton_of_forall_mem_eq
