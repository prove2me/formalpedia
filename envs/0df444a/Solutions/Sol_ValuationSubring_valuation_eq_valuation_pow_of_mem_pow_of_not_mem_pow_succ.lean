-- Prove2me | solution 1 for ValuationSubring.valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/97c4b35c-cd8f-5112-9801-17b22ffcd107

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ

set_option autoImplicit false

open NumberField

namespace IIB_node13

p2m_open "Ideal NumberField.Ideal UniqueFactorizationMonoid"

theorem main
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (M : Type) [Field M] [NumberField M] [Algebra M (AlgebraicClosure ℚ)]
    (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (hQle : ∀ x : 𝓞 M, P.valuation (algebraMap M (AlgebraicClosure ℚ) x) ≤ 1)
    (hQlt : ∀ x : 𝓞 M, x ∈ Q ↔ P.valuation (algebraMap M (AlgebraicClosure ℚ) x) < 1)
    (π : 𝓞 M) (hπ : π ∈ Q) (hπ2 : π ∉ Q ^ 2) :
    ∀ (n : ℕ) (x : 𝓞 M), x ∈ Q ^ n → x ∉ Q ^ (n + 1) →
      P.valuation (algebraMap M (AlgebraicClosure ℚ) x) =
        P.valuation (algebraMap M (AlgebraicClosure ℚ) π) ^ n := by

  set v : 𝓞 M → P.ValueGroup := fun a => P.valuation (algebraMap M (AlgebraicClosure ℚ) a) with hv
  have hvmul : ∀ a b : 𝓞 M, v (a * b) = v a * v b := by
    intro a b
    simp only [hv, RingOfIntegers.coe_eq_algebraMap, map_mul]
  have hv1 : ∀ a : 𝓞 M, a ∉ Q → v a = 1 := by
    intro a ha
    exact le_antisymm (hQle a) (not_lt.mp (mt (hQlt a).mpr ha))

  have hQ0 : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField ‹_› (RingOfIntegers.not_isField M)
  have hQ0' : Q ≠ 0 := hQ0
  have hπ0 : (Ideal.span {π} : Ideal (𝓞 M)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    rintro rfl
    exact hπ2 (Submodule.zero_mem _)
  obtain ⟨J, hQJ, hfac⟩ := eq_prime_pow_mul_coprime hπ0 Q
  have hcount : Multiset.count Q (normalizedFactors (Ideal.span {π})) = 1 :=
    Ideal.count_normalizedFactors_eq
      (by rw [pow_one, Ideal.span_singleton_le_iff_mem]; exact hπ)
      (by rw [Ideal.span_singleton_le_iff_mem]; exact hπ2)
  rw [hcount, pow_one] at hfac

  have hJQ : ¬ J ≤ Q := fun h => by
    have hQJ' : Q ⊔ J = Q := sup_eq_left.mpr h
    rw [hQJ'] at hQJ
    exact (IsMaximal.ne_top ‹_›) hQJ
  obtain ⟨s, hsJ, hsQ⟩ := (SetLike.not_le_iff_exists.mp hJQ)
  have hcop : IsCoprime Q J := Ideal.isCoprime_iff_sup_eq.mpr hQJ
  intro n
  induction n with
  | zero =>
    intro x _ hx'
    rw [zero_add, pow_one] at hx'
    rw [pow_zero]
    exact hv1 x hx'
  | succ n ih =>
    intro x hx hx'

    have hxs : x * s ∈ Q * J := Ideal.mul_mem_mul (Ideal.pow_le_self n.succ_ne_zero hx) hsJ
    rw [← hfac] at hxs
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hxs
    have hzπ : z * π ∈ Q ^ (n + 1) := by
      rw [hz]
      exact Ideal.mul_mem_right s _ hx
    have hzn : z ∈ Q ^ n := by
      have h1 : Q ^ (n + 1) ∣ Ideal.span {z} * Ideal.span {π} := by
        rw [Ideal.span_singleton_mul_span_singleton, Ideal.dvd_span_singleton]
        exact hzπ
      rw [hfac, pow_succ', mul_left_comm, mul_dvd_mul_iff_left hQ0'] at h1
      exact (Ideal.dvd_span_singleton).mp ((hcop.pow_left).dvd_of_dvd_mul_right h1)
    have hzn' : z ∉ Q ^ (n + 1) := by
      intro hz'
      have hxs2 : x * s ∈ Q ^ (n + 1 + 1) := by
        rw [← hz, pow_succ]
        exact Ideal.mul_mem_mul hz' hπ
      rcases Ideal.IsPrime.mem_pow_mul Q hxs2 with h | h
      · exact hx' h
      · exact hsQ h
    have hvz : v z = v π ^ n := ih z hzn hzn'
    have key : v x * v s = v z * v π := by
      rw [← hvmul, ← hvmul, hz]
    rw [hv1 s hsQ, mul_one, hvz, ← pow_succ] at key
    exact key

end IIB_node13

theorem solution
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (M : Type) [Field M] [NumberField M] [Algebra M (AlgebraicClosure ℚ)]
    (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (hQle : ∀ x : 𝓞 M, P.valuation (algebraMap M (AlgebraicClosure ℚ) x) ≤ 1)
    (hQlt : ∀ x : 𝓞 M, x ∈ Q ↔ P.valuation (algebraMap M (AlgebraicClosure ℚ) x) < 1)
    (π : 𝓞 M) (hπ : π ∈ Q) (hπ2 : π ∉ Q ^ 2)
    (n : ℕ) (x : 𝓞 M) (hx : x ∈ Q ^ n) (hx' : x ∉ Q ^ (n + 1)) :
    P.valuation (algebraMap M (AlgebraicClosure ℚ) x) = P.valuation (algebraMap M (AlgebraicClosure ℚ) π) ^ n :=
  IIB_node13.main P M Q hQle hQlt π hπ hπ2 n x hx hx'

end S_ValuationSubring_valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ
end P2MW
export P2MW.S_ValuationSubring_valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ (solution)
