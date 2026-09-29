-- Prove2me | solution 1 for RingTheory.Sequence.isRegular_pair_of_isSMulRegular_of_isReduced_of_forall_notMem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4d314fa5-c14b-5823-8654-217869c40e5d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingTheory_Sequence_isRegular_pair_of_isSMulRegular_of_isReduced_of_forall_notMem_minimalPrimes

set_option autoImplicit false

namespace RegPair

theorem mem_nonZeroDivisors_of_forall_notMem_minimalPrimes {S : Type*} [CommRing S] [IsReduced S] (x : S)
    (hx : ∀ P ∈ minimalPrimes S, x ∉ P) : x ∈ nonZeroDivisors S := by
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  by_contra hy0

  have hnil : y ∉ nilradical S := by rw [nilradical_eq_zero]; exact hy0
  rw [nilradical_eq_sInf, Submodule.mem_sInf] at hnil
  push Not at hnil
  obtain ⟨J, hJ, hyJ⟩ := hnil

  haveI : Ideal.IsPrime J := hJ
  obtain ⟨P, hP, hPJ⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal S) ≤ (J : Ideal S) from bot_le)
  have hPmin : P ∈ minimalPrimes S := hP
  haveI : P.IsPrime := hP.1.1
  have hxy : y * x ∈ P := by rw [hy]; exact P.zero_mem
  rcases (Ideal.IsPrime.mem_or_mem inferInstance hxy) with h | h
  · exact hyJ (hPJ h)
  · exact hx P hPmin h

end RegPair

theorem solution
    {A : Type*} [CommRing A] [IsLocalRing A] {B : Type*} [CommRing B] [Nontrivial B] [Algebra A B] [Module.Finite A B]
    (a b : A) (ha𝔪 : a ∈ IsLocalRing.maximalIdeal A) (hb𝔪 : b ∈ IsLocalRing.maximalIdeal A)
    (ha : IsSMulRegular B (algebraMap A B a))
    (hred : IsReduced (B ⧸ Ideal.span {algebraMap A B a}))
    (hb : ∀ P ∈ minimalPrimes (B ⧸ Ideal.span {algebraMap A B a}),
      Ideal.Quotient.mk (Ideal.span {algebraMap A B a}) (algebraMap A B b) ∉ P) :
    RingTheory.Sequence.IsRegular B [a, b] := by
  refine RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal B (fun r hr => ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ha𝔪
    · exact hb𝔪
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff]
  refine ⟨?_, ?_, RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩
  ·
    intro x y h
    exact ha (by simp only [Algebra.smul_def] at h; exact h)
  ·
    have hnzd := RegPair.mem_nonZeroDivisors_of_forall_notMem_minimalPrimes _ hb
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro x hx
    rw [Submodule.mem_smul_pointwise_iff_exists] at hx ⊢
    obtain ⟨z, -, hz⟩ := hx

    have hq : Ideal.Quotient.mk (Ideal.span {algebraMap A B a}) (algebraMap A B b) *
        Ideal.Quotient.mk (Ideal.span {algebraMap A B a}) x = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      refine ⟨z, ?_⟩
      rw [← Algebra.smul_def, ← hz, Algebra.smul_def]
    have hx0 := (mem_nonZeroDivisors_iff_right.mp hnzd) _ (by rwa [mul_comm] at hq)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx0
    obtain ⟨w, hw⟩ := hx0
    exact ⟨w, trivial, by rw [Algebra.smul_def, hw]⟩

end S_RingTheory_Sequence_isRegular_pair_of_isSMulRegular_of_isReduced_of_forall_notMem_minimalPrimes
end P2MW
export P2MW.S_RingTheory_Sequence_isRegular_pair_of_isSMulRegular_of_isReduced_of_forall_notMem_minimalPrimes (solution)
