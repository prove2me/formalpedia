-- Prove2me | solution 1 for ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/26034757-0ce0-5f0b-aa21-9acd96f967b5

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one

theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (q m : ℕ)
    (hA : A.LiesOverPrime q) (hσ : A.IsFrobeniusAt σ q) (hm : m.Coprime q)
    (ζ : L) (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ q := by
  classical

  set k := IsLocalRing.ResidueField A with hk
  have hqA : ((q : A) : L) ∈ A.nonunits := by push_cast; exact hA
  have hq𝔪 : (q : A) ∈ IsLocalRing.maximalIdeal A := ValuationSubring.coe_mem_nonunits_iff.mp hqA
  have hqk : (q : k) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]; exact hq𝔪

  have hmk : (m : k) ≠ 0 := by
    intro hm0
    have h1 : ringChar k ∣ m := (CharP.cast_eq_zero_iff k (ringChar k) m).mp hm0
    have h2 : ringChar k ∣ q := (CharP.cast_eq_zero_iff k (ringChar k) q).mp hqk
    have h3 : ringChar k ∣ Nat.gcd m q := Nat.dvd_gcd h1 h2
    rw [hm.gcd_eq_one, Nat.dvd_one] at h3
    exact CharP.ringChar_ne_one h3

  have hm0 : m ≠ 0 := by
    rintro rfl
    have hq1 : q = 1 := by simpa using hm
    subst hq1
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      ((Ideal.eq_top_iff_one _).mpr (by simp at hq𝔪))

  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [zero_pow hm0] at hζ; exact zero_ne_one hζ
  have hζA : ζ ∈ A := by
    rcases A.mem_or_inv_mem ζ with h | h
    · exact h
    · have : ζ = (ζ⁻¹) ^ (m - 1) := by
        rw [inv_pow]
        refine (inv_eq_of_mul_eq_one_right ?_).symm
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0), hζ]
      rw [this]; exact pow_mem h _

  set g : A.decompositionSubgroup K := ⟨σ, hσ.mem_decompositionSubgroup⟩ with hg
  set a : A := ⟨ζ, hζA⟩ with ha
  set b : A := g • a with hb
  have hbL : ((b : A) : L) = σ ζ := rfl
  have ham : a ^ m = 1 := Subtype.ext (by simp [ha, hζ])
  have hbm : b ^ m = 1 := by rw [hb, ← smul_pow', ham, smul_one]
  set v : A := a ^ q with hv
  have hvm : v ^ m = 1 := by rw [hv, ← pow_mul, mul_comm, pow_mul, ham, one_pow]

  have hres : IsLocalRing.residue A b = IsLocalRing.residue A v := by
    rw [hb, IsLocalRing.ResidueField.residue_smul, hg, hσ.smul_residue_eq, hv, map_pow]

  set S : A := ∑ i ∈ Finset.range m, b ^ i * v ^ (m - 1 - i) with hS
  have hSbv : S * (b - v) = 0 := by rw [hS, geom_sum₂_mul, hbm, hvm, sub_self]

  have hresv_ne : IsLocalRing.residue A v ≠ 0 := by
    have h1 : IsLocalRing.residue A v ^ m = 1 := by rw [← map_pow, hvm, map_one]
    exact ne_zero_pow hm0 (by rw [h1]; exact one_ne_zero)
  have hresS : IsLocalRing.residue A S
      = (m : k) * IsLocalRing.residue A v ^ (m - 1) := by
    rw [hS, map_sum]
    have : ∀ i ∈ Finset.range m, IsLocalRing.residue A (b ^ i * v ^ (m - 1 - i))
        = IsLocalRing.residue A v ^ (m - 1) := by
      intro i hi
      have him : i < m := Finset.mem_range.mp hi
      rw [map_mul, map_pow, map_pow, hres, ← pow_add]
      congr 1; omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hSunit : IsUnit S := by
    by_contra hSu
    have hS𝔪 : S ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal S).mpr hSu
    have h0 : IsLocalRing.residue A S = 0 := (IsLocalRing.residue_eq_zero_iff S).mpr hS𝔪
    rw [hresS] at h0
    exact (mul_ne_zero hmk (pow_ne_zero _ hresv_ne)) h0
  have hbv : b = v := sub_eq_zero.mp ((hSunit.mul_right_eq_zero).mp hSbv)

  have := congrArg (fun z : A => (z : L)) hbv
  simpa [hbL, hv, ha] using this

end S_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one
end P2MW
export P2MW.S_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one (solution)
