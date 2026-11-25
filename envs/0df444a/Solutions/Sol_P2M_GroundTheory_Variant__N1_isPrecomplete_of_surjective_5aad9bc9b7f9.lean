-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_isPrecomplete_of_surjective_5aad9bc9b7f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:46:03.649832+00:00
-- url     : https://prove2.me/submissions/f2451ba7-4da1-4ee5-9b84-15fe3eac595c

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_PrecompleteOfSurjective
import Theorems.Thm_P2M_GroundTheory_Variant__N1_smodEq_span_singleton_pow_iff_1a3f4e200796

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
namespace GroundTheory.Variant₂.N1
theorem _root_.solution {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (a : A) [IsPrecomplete (Ideal.span {a}) A] :
    IsPrecomplete (Ideal.span {f a}) B := by
  refine ⟨fun b hb => ?_⟩
  have hb' : ∀ {m n : ℕ}, m ≤ n → f a ^ m ∣ b m - b n := fun hmn =>
    (smodEq_span_singleton_pow_iff (f a) _ _ _).1 (hb hmn)
  have hstep : ∀ n : ℕ, ∃ x : A, b (n + 1) = b n + f (a ^ n * x) := by
    intro n
    obtain ⟨c, hc⟩ := hb' (Nat.le_add_right n 1)
    obtain ⟨x, rfl⟩ := hf c
    refine ⟨-x, ?_⟩
    rw [map_mul, map_pow, map_neg]
    linear_combination -hc
  choose x hx using hstep
  obtain ⟨y₀, hy₀⟩ := hf (b 0)
  let y : ℕ → A := fun n => y₀ + ∑ k ∈ Finset.range n, a ^ k * x k
  have hy_succ : ∀ n, y (n + 1) = y n + a ^ n * x n := by
    intro n
    simp only [y, Finset.sum_range_succ, add_assoc]
  have hy : ∀ n, f (y n) = b n := by
    intro n
    induction n with
    | zero => simp [y, hy₀]
    | succ n ih => rw [hy_succ, map_add, ih, hx]
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → a ^ m ∣ y m - y n := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hy_succ, sub_add_eq_sub_sub]
      exact dvd_sub ih (Dvd.dvd.mul_right (pow_dvd_pow a hmn) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {a}) inferInstance (f := y)
    (fun {m n} hmn => (smodEq_span_singleton_pow_iff a m _ _).2 (hcauchy hmn))
  refine ⟨f L, fun n => (smodEq_span_singleton_pow_iff (f a) n _ _).2 ?_⟩
  have h := map_dvd f ((smodEq_span_singleton_pow_iff a n _ _).1 (hL n))
  rwa [map_pow, map_sub, hy] at h
end GroundTheory.Variant₂.N1
