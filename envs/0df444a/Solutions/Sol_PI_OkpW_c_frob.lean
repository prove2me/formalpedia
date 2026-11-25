-- Prove2me | solution 1 for PI.OkpW.c_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:17:09.515844+00:00
-- url     : https://prove2.me/submissions/fdeac1ec-0998-414c-a184-c11757177905

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_CFixRat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_CFrob
import Theorems.Thm_PI_OkpW_add_c_int
import Theorems.Thm_PI_OkpW_finite_quot
import Theorems.Thm_PI_OkpW_isMaximal_span_p
import Theorems.Thm_PI_OkpW_natCard_quot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.OkpW
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]
namespace PI.OkpW
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (c : K →+* K) (hc : ∃ x, c x ≠ x) (hp2 : p ≠ 2)
    (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) (a : 𝓞 K) :
    (p : 𝓞 K) ∣ RingOfIntegers.mapRingHom c a - a ^ p := by
  classical
  haveI hmax := isMaximal_span_p (K := K) (p := p) hP
  have hle : Ideal.span {(p : 𝓞 K)} ≤
      (Ideal.span {(p : 𝓞 K)}).comap (RingOfIntegers.mapRingHom c) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show RingOfIntegers.mapRingHom c (p : 𝓞 K) ∈ Ideal.span {(p : 𝓞 K)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  let σ : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) →+* (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) := Ideal.quotientMap _ (RingOfIntegers.mapRingHom c) hle
  have hσ : ∀ y : 𝓞 K, σ (Ideal.Quotient.mk _ y) =
      Ideal.Quotient.mk _ (RingOfIntegers.mapRingHom c y) := fun y => Ideal.quotientMap_mk
  haveI : CharP (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) p := CharP.quotient (𝓞 K) p
    (mem_nonunits_iff.mpr fun hu => hP.ne_top (Ideal.span_singleton_eq_top.mpr hu))
  haveI : ExpChar (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) p := ExpChar.prime hp.out
  have h2 : (2 : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) = 0 := by exact_mod_cast h
    have hd := (CharP.cast_eq_zero_iff (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) p 2).mp h'
    have hp3 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have := hp.out.two_le
    omega
  have hfixZ : ∀ z : ℤ, ((z : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}))) ^ p = z := fun z => by rw [← frobenius_def, map_intCast]
  have h2p : (2 : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) ^ p = 2 := by rw [← frobenius_def, map_ofNat]
  have hdich : ∀ x : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}), x ^ p = x ∨ x ^ p = σ x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨n, hn⟩ := add_c_int hK c hc a
    obtain ⟨n2, hn2⟩ := add_c_int hK c hc (a ^ 2)
    have ht : Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a +
        σ (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a) = (n : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) := by
      rw [hσ, ← map_add, hn, map_intCast]
    have ht2 : Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a ^ 2 +
        σ (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a) ^ 2 = (n2 : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) := by
      have := congrArg (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)})) hn2
      rw [map_add, map_intCast, map_pow, map_pow] at this
      rw [hσ, ← this, map_pow (Ideal.Quotient.mk _) ((RingOfIntegers.mapRingHom c) a)]
    generalize Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a = x at ht ht2 ⊢
    have hm : (2 : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) * (x * σ x) = (n : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) ^ 2 - n2 := by
      rw [← ht, ← ht2]; ring
    have hmp : (x * σ x) ^ p = x * σ x := by
      have h1 : ((2 : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) * (x * σ x)) ^ p = 2 * (x * σ x) := by
        rw [hm, sub_pow_char, ← pow_mul, mul_comm 2 p, pow_mul, hfixZ, hfixZ]
      rw [mul_pow, h2p] at h1
      exact mul_left_cancel₀ h2 h1
    have hzero : x ^ 2 - (n : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) * x + x * σ x = 0 := by
      rw [← ht]; ring
    have hfr := congrArg (frobenius (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) p) hzero
    rw [map_zero, map_add, map_sub, map_mul, map_pow, map_intCast, frobenius_def,
      frobenius_def, hmp] at hfr
    have hq : (x ^ p - x) * (x ^ p - σ x) = 0 := by
      rw [← hfr, ← ht]; ring
    rcases mul_eq_zero.mp hq with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have hex : ∃ y : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}), y ^ p ≠ y := by
    by_contra hcon
    push_neg at hcon
    haveI := finite_quot (K := K) (p := p) hK
    letI := Fintype.ofFinite (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})
    letI : Field (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) := Ideal.Quotient.field _
    have hp1 : 1 < p := hp.out.one_lt
    have hsub : (Finset.univ : Finset (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) ⊆ ((Polynomial.X ^ p - Polynomial.X : Polynomial (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})).roots.toFinset) := by
      intro y _
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) hp1)]
      simp [Polynomial.IsRoot, hcon y]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ] at h1
    have h2 := (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' (Polynomial.X ^ p - Polynomial.X : Polynomial (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})))
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) hp1] at h2
    have h3 : Fintype.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
      rw [← Nat.card_eq_fintype_card]; exact natCard_quot (K := K) (p := p) hK
    have h4 : p ^ 2 ≤ p := h3 ▸ h1.trans h2
    nlinarith [hp1]
  obtain ⟨y, hy⟩ := hex
  have hyσ : y ^ p = σ y := (hdich y).resolve_left hy
  have hall : ∀ x : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}), σ x = x ^ p := by
    intro x
    rcases hdich x with hx | hx
    · have hxy : (x + y) ^ p ≠ x + y := by
        rw [add_pow_char, hx]
        intro h
        exact hy (add_left_cancel h)
      have h1 := (hdich (x + y)).resolve_left hxy
      rw [add_pow_char, hx, hyσ, map_add] at h1
      rw [hx]
      exact (add_right_cancel h1).symm
    · exact hx.symm
  have := hall (Ideal.Quotient.mk _ a)
  rw [hσ, ← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at this
  exact this
end PI.OkpW
