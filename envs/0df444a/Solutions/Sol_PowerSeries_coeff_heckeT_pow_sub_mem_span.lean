-- Prove2me | solution 1 for PowerSeries.coeff_heckeT_pow_sub_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c40474e2-7594-5b43-a135-a21a3f8bed1d

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Theorems.Thm_CuspForm_qCoeff_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_coeff_heckeT_pow_sub_mem_span

set_option autoImplicit false

open CuspForm ModularFormClass

private lemma pow_congr_of_dvd_sub (p : ℕ) [Fact p.Prime] {ℓ : ℕ} (hℓp : ¬ p ∣ ℓ)
    (a b : ℕ) (hab : (p - 1 : ℕ) ∣ b - a) (hba : a ≤ b) :
    (ℓ : integralClosure ℤ ℂ) ^ b - (ℓ : integralClosure ℤ ℂ) ^ a ∈
      Ideal.span {(p : integralClosure ℤ ℂ)} := by
  obtain ⟨t, ht⟩ := hab
  have hz : (p : ℤ) ∣ ℓ ^ (b - a) - 1 := by
    have h0 : ((ℓ ^ (b - a) - 1 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [ht, pow_mul, ZMod.pow_card_sub_one_eq_one (by
        intro h
        apply hℓp
        have h' : ((ℓ : ℤ) : ZMod p) = 0 := by exact_mod_cast h
        exact Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h')), one_pow]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  obtain ⟨u, hu⟩ := hz
  have hsplit : (ℓ : integralClosure ℤ ℂ) ^ b =
      (ℓ : integralClosure ℤ ℂ) ^ a * (ℓ : integralClosure ℤ ℂ) ^ (b - a) := by
    rw [← pow_add]
    congr 1
    omega
  refine Ideal.mem_span_singleton.mpr ⟨(ℓ : integralClosure ℤ ℂ) ^ a * (u : integralClosure ℤ ℂ), ?_⟩
  have hcast := congrArg (fun z : ℤ => ((z : ℤ) : integralClosure ℤ ℂ)) hu
  push_cast at hcast
  rw [hsplit]
  linear_combination (ℓ : integralClosure ℤ ℂ) ^ a * hcast

theorem solution (p : ℕ) [Fact p.Prime] {N : ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform)
    (a : ℕ → integralClosure ℤ ℂ) (ha : ∀ n : ℕ, (a n : ℂ) = ModularFormClass.qCoeff f n)
    (j k : ℕ) (hk : 2 ≤ k) (hk2 : (p - 1 : ℕ) ∣ k - 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.heckeT ℓ k (PowerSeries.mk fun m => a m ^ p ^ j))
      - a ℓ ^ p ^ j * a n ^ p ^ j ∈ Ideal.span {(p : integralClosure ℤ ℂ)}:= by
  have hp' : p.Prime := Fact.out
  have hP0 : p ^ j ≠ 0 := pow_ne_zero _ hp'.ne_zero
  rw [PowerSeries.coeff_heckeT]
  simp only [PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  ·
    subst hn0
    have ha0 : a 0 = 0 := by
      apply Subtype.coe_injective
      show ((a 0 : integralClosure ℤ ℂ) : ℂ) = ((0 : integralClosure ℤ ℂ) : ℂ)
      rw [ha 0]
      simpa using CuspForm.qCoeff_zero f
    simp [ha0, zero_pow hP0, Nat.zero_div, mul_zero]
  by_cases hdvd : ℓ ∣ n
  ·
    have hn0 : n ≠ 0 := hnpos.ne'
    set e : ℕ := n.factorization ℓ with hedef
    have he1 : 1 ≤ e := (hℓ.factorization_pos_of_dvd hn0 hdvd)
    set m : ℕ := n / ℓ ^ e with hmdef
    have hℓm : ¬ ℓ ∣ m := Nat.not_dvd_ordCompl hℓ hn0
    have hcopm : ∀ r : ℕ, Nat.Coprime (ℓ ^ r) m := fun r =>
      (hℓ.coprime_iff_not_dvd.mpr hℓm).pow_left _
    have hn : n = ℓ ^ e * m := (Nat.ordProj_mul_ordCompl_eq_self n ℓ).symm
    have hℓn : ℓ * n = ℓ ^ (e + 1) * m := by
      rw [hn, pow_succ]
      ring
    have hndiv : n / ℓ = ℓ ^ (e - 1) * m := by
      rw [hn, show (ℓ : ℕ) ^ e = ℓ * ℓ ^ (e - 1) from by
        rw [← pow_succ']
        congr 1
        omega]
      rw [mul_assoc]
      exact Nat.mul_div_cancel_left _ hℓ.pos

    have haℓn : a (ℓ * n) = a ℓ * a n - (ℓ : integralClosure ℤ ℂ) * a (n / ℓ) := by
      apply Subtype.coe_injective
      push_cast
      rw [ha, ha, ha, ha, hℓn, hndiv, hn,
        hf.qCoeff_mul_of_coprime _ _ (hcopm (e + 1)),
        hf.qCoeff_mul_of_coprime _ _ (hcopm e),
        hf.qCoeff_mul_of_coprime _ _ (hcopm (e - 1)),
        show e + 1 = (e - 1) + 2 from by omega,
        hf.qCoeff_prime_pow_of_not_dvd ℓ (e - 1) hℓ hℓN,
        show (e - 1) + 1 = e from by omega]
      ring

    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp'
      (a (ℓ * n)) ((ℓ : integralClosure ℤ ℂ) * a (n / ℓ)) j
    have hsum : a (ℓ * n) + (ℓ : integralClosure ℤ ℂ) * a (n / ℓ) = a ℓ * a n := by
      rw [haℓn]
      ring
    rw [hsum] at hr

    have hexp : (ℓ : integralClosure ℤ ℂ) ^ (k - 1) - (ℓ : integralClosure ℤ ℂ) ^ p ^ j ∈
        Ideal.span {(p : integralClosure ℤ ℂ)} := by
      by_cases hℓp : ℓ = p
      · subst hℓp
        refine Ideal.mem_span_singleton.mpr ⟨(ℓ : integralClosure ℤ ℂ) ^ (k - 2) -
          (ℓ : integralClosure ℤ ℂ) ^ (ℓ ^ j - 1), ?_⟩
        have h1 : (ℓ : integralClosure ℤ ℂ) ^ (k - 1) =
            (ℓ : integralClosure ℤ ℂ) * (ℓ : integralClosure ℤ ℂ) ^ (k - 2) := by
          rw [← pow_succ']
          congr 1
          omega
        have h2 : (ℓ : integralClosure ℤ ℂ) ^ ℓ ^ j =
            (ℓ : integralClosure ℤ ℂ) * (ℓ : integralClosure ℤ ℂ) ^ (ℓ ^ j - 1) := by
          rw [← pow_succ']
          congr 1
          have := Nat.one_le_pow j ℓ hℓ.pos
          omega
        rw [h1, h2]
        ring
      · have hpℓ : ¬ p ∣ ℓ := fun hd => hℓp ((Nat.prime_dvd_prime_iff_eq hp' hℓ).mp hd).symm
        have h1 := pow_congr_of_dvd_sub p hpℓ 1 (k - 1)
          (by rw [show (k - 1) - 1 = k - 2 from by omega]; exact hk2) (by omega)
        have hnatdvd : (p - 1 : ℕ) ∣ p ^ j - 1 := by
          have hZ : ((p : ℤ) - 1) ∣ (p : ℤ) ^ j - 1 := by
            simpa using sub_dvd_pow_sub_pow (p : ℤ) 1 j
          have e1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
            rw [Nat.cast_sub hp'.one_lt.le, Nat.cast_one]
          have e2 : ((p ^ j - 1 : ℕ) : ℤ) = (p : ℤ) ^ j - 1 := by
            rw [Nat.cast_sub (Nat.one_le_pow j p hp'.pos), Nat.cast_one, Nat.cast_pow]
          exact Int.natCast_dvd_natCast.mp (by rw [e1, e2]; exact hZ)
        have h2 := pow_congr_of_dvd_sub p hpℓ 1 (p ^ j)
          (by simpa using hnatdvd) (Nat.one_le_pow _ _ hp'.pos)
        have := Ideal.sub_mem _ h1 h2
        simpa using this

    simp only [if_pos hdvd]
    have hfin : a (ℓ * n) ^ p ^ j +
        (ℓ : integralClosure ℤ ℂ) ^ (k - 1) * a (n / ℓ) ^ p ^ j -
        a ℓ ^ p ^ j * a n ^ p ^ j =
        ((ℓ : integralClosure ℤ ℂ) ^ (k - 1) - (ℓ : integralClosure ℤ ℂ) ^ p ^ j) *
          a (n / ℓ) ^ p ^ j -
        (p : integralClosure ℤ ℂ) *
          (a (ℓ * n) * ((ℓ : integralClosure ℤ ℂ) * a (n / ℓ)) * r) := by
      have hmp : (a ℓ * a n) ^ p ^ j = a ℓ ^ p ^ j * a n ^ p ^ j := mul_pow _ _ _
      have hlp : ((ℓ : integralClosure ℤ ℂ) * a (n / ℓ)) ^ p ^ j =
          (ℓ : integralClosure ℤ ℂ) ^ p ^ j * a (n / ℓ) ^ p ^ j := mul_pow _ _ _
      linear_combination hmp - hr - hlp
    rw [hfin]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hexp)
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _)))
  ·
    have hcop : Nat.Coprime ℓ n := hℓ.coprime_iff_not_dvd.mpr hdvd
    have haℓn : a (ℓ * n) = a ℓ * a n := by
      apply Subtype.coe_injective
      push_cast
      rw [ha, ha, ha, hf.qCoeff_mul_of_coprime _ _ hcop]
    simp only [if_neg hdvd, mul_zero, add_zero]
    rw [haℓn, mul_pow]
    simp

end S_PowerSeries_coeff_heckeT_pow_sub_mem_span
end P2MW
export P2MW.S_PowerSeries_coeff_heckeT_pow_sub_mem_span (solution)
