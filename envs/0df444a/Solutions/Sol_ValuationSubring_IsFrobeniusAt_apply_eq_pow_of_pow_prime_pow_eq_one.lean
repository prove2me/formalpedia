-- Prove2me | solution 1 for ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_prime_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/4caab809-578a-5097-a0b3-29955e59c5f1

import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_prime_pow_eq_one

private theorem apply_eq_pow_of_pow_eq_one_of_not_dvd
    {q n : ℕ} (hq : q.Prime) (hn : ¬ q ∣ n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : A.IsFrobeniusAt σ q)
    (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ n = 1) :
    σ ζ = ζ ^ q := by
  classical
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (dvd_zero q)

  have hζA : ζ ∈ A := by
    rcases A.mem_or_inv_mem ζ with h | h
    · exact h
    · have h1 : ζ ^ (n - 1) * ζ = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0), hζ]
      have h2 : ζ⁻¹ ^ (n - 1) = ζ := by
        rw [inv_pow]
        exact inv_eq_of_mul_eq_one_right h1
      rw [← h2]
      exact pow_mem h (n - 1)

  have hu : σ ζ ∈ A :=
    ((⟨σ, hσ.mem_decompositionSubgroup⟩ : A.decompositionSubgroup ℚ) • (⟨ζ, hζA⟩ : A)).2
  have hw : ζ ^ q ∈ A := pow_mem hζA q

  have hap : (⟨σ ζ, hu⟩ : A) ^ n = 1 := by
    have h1 : (σ ζ) ^ n = 1 := by rw [← map_pow, hζ, map_one]
    exact Subtype.ext (by push_cast; exact h1)
  have hbp : (⟨ζ ^ q, hw⟩ : A) ^ n = 1 := by
    have h1 : (ζ ^ q) ^ n = 1 := by rw [← pow_mul, mul_comm q n, pow_mul, hζ, one_pow]
    exact Subtype.ext (by push_cast; exact h1)

  have hres : IsLocalRing.residue A (⟨σ ζ, hu⟩ : A) =
      IsLocalRing.residue A (⟨ζ ^ q, hw⟩ : A) := by
    have h1 := hσ.smul_residue_eq (IsLocalRing.residue A (⟨ζ, hζA⟩ : A))
    rw [← IsLocalRing.ResidueField.residue_smul] at h1
    rw [show (⟨σ, hσ.mem_decompositionSubgroup⟩ : A.decompositionSubgroup ℚ) • (⟨ζ, hζA⟩ : A)
        = ⟨σ ζ, hu⟩ from Subtype.ext rfl] at h1
    rw [← map_pow] at h1
    rw [show (⟨ζ, hζA⟩ : A) ^ q = ⟨ζ ^ q, hw⟩ from Subtype.ext (by push_cast; rfl)] at h1
    exact h1

  by_contra hne
  have hab : (⟨σ ζ, hu⟩ : A) - ⟨ζ ^ q, hw⟩ ≠ 0 := by
    intro h
    exact hne (congrArg Subtype.val (sub_eq_zero.mp h))
  have key : (∑ i ∈ Finset.range n, (⟨σ ζ, hu⟩ : A) ^ i * (⟨ζ ^ q, hw⟩ : A) ^ (n - 1 - i)) *
      ((⟨σ ζ, hu⟩ : A) - ⟨ζ ^ q, hw⟩) = 0 := by
    rw [geom_sum₂_mul, hap, hbp, sub_self]
  have hS : (∑ i ∈ Finset.range n, (⟨σ ζ, hu⟩ : A) ^ i * (⟨ζ ^ q, hw⟩ : A) ^ (n - 1 - i)) = 0 :=
    (mul_eq_zero.mp key).resolve_right hab

  have hsum : (n : IsLocalRing.ResidueField A) *
      IsLocalRing.residue A (⟨ζ ^ q, hw⟩ : A) ^ (n - 1) = 0 := by
    have h0 := congrArg (IsLocalRing.residue A) hS
    rw [map_sum, _root_.map_zero] at h0
    have h1 : ∀ i ∈ Finset.range n,
        IsLocalRing.residue A ((⟨σ ζ, hu⟩ : A) ^ i * (⟨ζ ^ q, hw⟩ : A) ^ (n - 1 - i))
          = IsLocalRing.residue A (⟨ζ ^ q, hw⟩ : A) ^ (n - 1) := by
      intro i hi
      have hip : i + (n - 1 - i) = n - 1 := by
        have := Finset.mem_range.mp hi
        omega
      rw [map_mul, map_pow, map_pow, hres, ← pow_add, hip]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h0
    exact h0

  have htne : IsLocalRing.residue A (⟨ζ ^ q, hw⟩ : A) ^ (n - 1) ≠ 0 := by
    apply pow_ne_zero
    intro h0
    have h1 : IsLocalRing.residue A (⟨ζ ^ q, hw⟩ : A) ^ n = 1 := by
      rw [← map_pow, hbp, map_one]
    rw [h0, zero_pow hn0] at h1
    exact zero_ne_one h1

  have hn' : (n : IsLocalRing.ResidueField A) = 0 := (mul_eq_zero.mp hsum).resolve_right htne
  haveI hchar : CharP (IsLocalRing.ResidueField A) q := by
    rw [CharP.charP_iff_prime_eq_zero hq]
    have hqA : ((q : A) : AlgebraicClosure ℚ) ∈ A.nonunits := by simp at hA ⊢; exact hA
    have hmax : (q : A) ∈ IsLocalRing.maximalIdeal A := A.coe_mem_nonunits_iff.mp hqA
    have hc : ((q : ℕ) : IsLocalRing.ResidueField A) = IsLocalRing.residue A ((q : ℕ) : A) := by
      simp
    rw [hc]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmax
  exact hn ((CharP.cast_eq_zero_iff _ q n).mp hn')

theorem solution
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : A.IsFrobeniusAt σ q)
    (k : ℕ) (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p ^ k = 1) :
    σ ζ = ζ ^ q :=
  apply_eq_pow_of_pow_eq_one_of_not_dvd hq
    (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h))) A hA hσ ζ hζ

end S_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_prime_pow_eq_one
end P2MW
export P2MW.S_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_prime_pow_eq_one (solution)
