-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.hensel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:28:26.050805+00:00
-- url     : https://prove2.me/submissions/2f81cb33-aa6c-45ad-baa4-3bb6f805acbd

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsAdicCompleteOfBasis
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_isAdicComplete_of_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {p : ℕ} [hp : Fact p.Prime]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution (f : ℤ_[p][X]) (hf : f.Monic) {m : ℕ} (hm0 : 0 < m) (hmp : ¬ p ∣ m) (Q0 : ℤ_[p][X])
    (h0 : ∃ K : ℤ_[p][X], AdjoinRoot.mk f (Q0 ^ m - 1) = (p : AdjoinRoot f) * AdjoinRoot.mk f K) :
    ∃ Q K : ℤ_[p][X], f ∣ Q ^ m - 1 ∧
      AdjoinRoot.mk f (Q - Q0) = (p : AdjoinRoot f) * AdjoinRoot.mk f K := by
  let S := AdjoinRoot f
  let J : Ideal S := Ideal.span {(p : S)}
  have : IsAdicComplete J S := isAdicComplete_of_basis S (AdjoinRoot.powerBasis' hf).basis
  have hHen : HenselianRing S J := inferInstance
  obtain ⟨K0, hK0⟩ := h0
  set a0 : S := AdjoinRoot.mk f Q0
  have ha0 : a0 ^ m - 1 ∈ J := by
    have : a0 ^ m - 1 = AdjoinRoot.mk f (Q0 ^ m - 1) := by simp [a0]
    rw [this, hK0]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hmon : (X ^ m - C (1 : S)).Monic := monic_X_pow_sub_C _ hm0.ne'
  have hev : (X ^ m - C (1 : S)).eval a0 ∈ J := by simpa using ha0
  have hu0 : IsUnit (Ideal.Quotient.mk J a0) := by
    have h1 : (Ideal.Quotient.mk J a0) ^ m = 1 := by
      rw [← map_pow, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.2 ha0
    exact IsUnit.of_pow_eq_one h1 hm0.ne'
  have hum : IsUnit (m : S ⧸ J) := by
    have hcop : Nat.Coprime m p :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hmp)
    have hg := Nat.gcd_eq_gcd_ab m p
    rw [hcop, Nat.cast_one] at hg
    have hp0 : (p : S ⧸ J) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk J)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    refine IsUnit.of_mul_eq_one ((Nat.gcdA m p : ℤ) : S ⧸ J) ?_
    have := congrArg (fun z : ℤ => (z : S ⧸ J)) hg
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, hp0, zero_mul,
      add_zero] at this
    exact this.symm
  have hder : IsUnit (Ideal.Quotient.mk J ((X ^ m - C (1 : S)).derivative.eval a0)) := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_natCast,
      eval_pow, eval_X, map_mul, map_pow, map_natCast]
    exact hum.mul (hu0.pow _)
  obtain ⟨a, ha, haJ⟩ := hHen.is_henselian _ hmon a0 hev hder
  obtain ⟨Q, rfl⟩ := AdjoinRoot.mk_surjective a
  refine ⟨Q, ?_⟩
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 haJ
  obtain ⟨K, rfl⟩ := AdjoinRoot.mk_surjective s
  refine ⟨K, ?_, ?_⟩
  · rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, map_one]
    simpa [IsRoot, sub_eq_zero] using ha
  · rw [map_sub, ← hs, mul_comm]
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
