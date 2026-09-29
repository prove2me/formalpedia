-- Prove2me | solution 1 for ValuationSubring.smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9b8556a6-8a8f-5a22-9034-250ad0c2fcf3

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one

set_option autoImplicit false

namespace P2mS17Roots

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

theorem charP_residueField_of_liesOverPrime {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) :
    CharP (IsLocalRing.ResidueField A) q := by
  have hq0 : ((q : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      ← ValuationSubring.coe_mem_nonunits_iff]
    have : ((((q : ℕ) : A)) : L) = ((q : ℕ) : L) := by simp
    rw [this]
    exact hA
  exact (CharP.charP_iff_prime_eq_zero hq).mpr hq0

theorem eq_one_of_residue_eq_one {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) {u : A} {m : ℕ} (hum : u ^ m = 1)
    (hm : ¬ q ∣ m) (hres : IsLocalRing.residue _ u = 1) : u = 1 := by
  haveI := charP_residueField_of_liesOverPrime A hq hA
  have hmκ : (m : IsLocalRing.ResidueField A) ≠ 0 := by
    rwa [Ne, CharP.cast_eq_zero_iff _ q]
  by_contra hu
  have h1 : (∑ i ∈ Finset.range m, u ^ i) * (u - 1) = 0 := by rw [geom_sum_mul, hum, sub_self]
  have h2 : ∑ i ∈ Finset.range m, u ^ i = 0 := (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hu)
  apply hmκ
  have := congrArg (IsLocalRing.residue A) h2
  rw [map_sum, map_zero] at this
  simpa [map_pow, hres] using this

theorem mem_of_pow_eq_one {ζ : L} {m : ℕ} (hm : m ≠ 0) (hζ : ζ ^ m = 1) : ζ ∈ A := by
  rw [← ValuationSubring.valuation_le_one_iff]
  have : (A.valuation ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
  exact ((pow_eq_one_iff_of_nonneg zero_le' hm).mp this).le

theorem smul_eq_pow_of_residue {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q)
    (σ : A.decompositionSubgroup K) (e : ℕ)
    (hσ : ∀ x : IsLocalRing.ResidueField A, σ • x = x ^ e)
    {ζ : L} {m : ℕ} (hm : ¬ q ∣ m) (hζ : ζ ^ m = 1) : (σ : L ≃ₐ[K] L) ζ = ζ ^ e := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  set z : A := ⟨ζ, mem_of_pow_eq_one A hm0 hζ⟩
  have hzm : z ^ m = 1 := Subtype.ext (by simp [z, hζ])
  have hres : IsLocalRing.residue _ (σ • z) = IsLocalRing.residue _ (z ^ e) := by
    rw [IsLocalRing.ResidueField.residue_smul, map_pow]
    exact hσ _
  have hw : (σ • z) * (z ^ (m - 1)) ^ e = 1 := by
    apply eq_one_of_residue_eq_one A hq hA (m := m) _ hm
    · rw [map_mul, hres, ← map_mul, ← mul_pow, ← pow_succ', Nat.sub_add_cancel hm1, hzm, one_pow, map_one]
    · rw [mul_pow, ← smul_pow', hzm, smul_one, one_mul, ← pow_mul, ← pow_mul,
        show (m - 1) * (e * m) = m * ((m - 1) * e) by ring, pow_mul, hzm, one_pow]
  have key : σ • z = z ^ e := by
    calc σ • z = (σ • z) * (z ^ (m - 1)) ^ e * z ^ e := by
          rw [mul_assoc, ← mul_pow, ← pow_succ, Nat.sub_add_cancel hm1, hzm, one_pow, mul_one]
      _ = z ^ e := by rw [hw, one_mul]
  have := congrArg Subtype.val key
  rwa [SubmonoidClass.coe_pow] at this

end P2mS17Roots

theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) {σ : L ≃ₐ[K] L} (hσ : A.IsFrobeniusAt σ q)
    {ζ : L} {m : ℕ} (hm : ¬ q ∣ m) (hζ : ζ ^ m = 1) : σ ζ = ζ ^ q :=
  P2mS17Roots.smul_eq_pow_of_residue A hq hA ⟨σ, hσ.mem_decompositionSubgroup⟩ q hσ.smul_residue_eq hm hζ

end S_ValuationSubring_smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one
end P2MW
export P2MW.S_ValuationSubring_smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one (solution)
