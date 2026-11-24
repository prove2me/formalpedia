-- Prove2me | solution 1 for Rat.seven_pid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:46:18.631026+00:00
-- url     : https://prove2.me/submissions/6eb420a1-6e6f-4a91-8b59-6ecbc9f786b0

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_FltRegular_SmallNumbers_Seven_Seven
public import Theorems.Thm_M7

set_option autoImplicit false
@[expose] public section
public section
open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers
  IsCyclotomicExtension.Rat Polynomial cyclotomic Ideal
variable {K : Type*} [Field K] [NumberField K]
local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)
variable [IsCyclotomicExtension {7} ℚ K]
variable (K)
namespace Rat
theorem _root_.solution : IsPrincipalIdealRing (𝓞 K) := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {7} ℚ K
  refine isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
    fun p hp hprime ↦ ?_
  have : (span {(p : ℤ)}).IsPrime :=
    isPrime_of_prime (prime_span_singleton_iff.mpr (prime_iff_prime_int.mp hprime))
  obtain ⟨⟨P, _, _⟩⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
  refine ⟨P, ⟨‹_›, ‹_›⟩, Or.inl ?_⟩
  rw [M7] at hp ⊢
  obtain ⟨h₁, h₄⟩ := Finset.mem_Icc.mp hp
  interval_cases p
  · norm_num at hprime
  · have h : orderOf (2 : ZMod 7) = 3 := (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩
    rw [inertiaDeg_eq_of_not_dvd (m := 7) 2 K P (by norm_num)]
    norm_num [h]
  · have h : orderOf (3 : ZMod 7) = 6 := (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩
    rw [inertiaDeg_eq_of_not_dvd (m := 7) 3 K P (by norm_num)]
    norm_num [h]
  · norm_num at hprime
end Rat
