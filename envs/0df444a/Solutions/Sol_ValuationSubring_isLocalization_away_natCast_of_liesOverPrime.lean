-- Prove2me | solution 1 for ValuationSubring.isLocalization_away_natCast_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e08493a2-3ff8-5e80-8a2f-4ddb19b4c777

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_isLocalization_away_natCast_of_liesOverPrime

set_option autoImplicit false

open AlgebraicGeometry

theorem solution
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p) :
    IsLocalization.Away ((p : ℕ) : ↥O) (AlgebraicClosure ℚ) := by
  classical
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpmax : ((p : ℕ) : ↥O) ∈ IsLocalRing.maximalIdeal ↥O := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hO
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    exact isUnit_iff_ne_zero.mpr (by
      show ((((p : ℕ) : ↥O) ^ n : ↥O) : AlgebraicClosure ℚ) ≠ 0
      push_cast
      exact pow_ne_zero _ hp0)
  · intro z
    have hz : IsAlgebraic ℤ z :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z)
    obtain ⟨d, hd0, hint⟩ := hz.exists_integral_multiple
    have hdz : (d : AlgebraicClosure ℚ) * z ∈ O := by
      have hi : IsIntegral ↥O ((d : AlgebraicClosure ℚ) * z) := by
        obtain ⟨f, hf, hfz⟩ := hint
        refine ⟨f.map (Int.castRingHom ↥O), hf.map _, ?_⟩
        rw [Polynomial.eval₂_map, show (algebraMap ↥O (AlgebraicClosure ℚ)).comp (Int.castRingHom ↥O) = algebraMap ℤ (AlgebraicClosure ℚ) from
          RingHom.ext (fun n => by simp), ← zsmul_eq_mul]
        exact hfz
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥O) (K := AlgebraicClosure ℚ)).mp hi
      rw [← hy]; exact y.2
    have habs : ((d.natAbs : ℕ) : AlgebraicClosure ℚ) * z ∈ O := by
      rcases le_or_gt 0 d with hd | hd
      · have hc : ((d.natAbs : ℕ) : AlgebraicClosure ℚ) = (d : AlgebraicClosure ℚ) := by rw [← Int.cast_natCast, Int.natAbs_of_nonneg hd]
        rw [hc]; exact hdz
      · have hc : ((d.natAbs : ℕ) : AlgebraicClosure ℚ) = -(d : AlgebraicClosure ℚ) := by rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hd.le, Int.cast_neg]
        rw [hc, show -(d : AlgebraicClosure ℚ) * z = -((d : AlgebraicClosure ℚ) * z) by ring]
        exact neg_mem hdz
    obtain ⟨n, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hd0) p hp.ne_one
    have hmunit : IsUnit ((m : ℕ) : ↥O) := by
      by_contra hmu
      have hm : ((m : ℕ) : ↥O) ∈ IsLocalRing.maximalIdeal ↥O := (IsLocalRing.mem_maximalIdeal _).mpr hmu
      have hcop : IsCoprime ((p : ℕ) : ℤ) ((m : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr hpm)
      obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom ↥O)
      have h1 : (1 : ↥O) ∈ IsLocalRing.maximalIdeal ↥O := by
        rw [← hab]
        refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
        · simpa using hpmax
        · simpa using hm
      exact (IsLocalRing.maximalIdeal.isMaximal ↥O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    obtain ⟨mu, hmu⟩ := hmunit
    have hmem : (p : AlgebraicClosure ℚ) ^ n * z ∈ O := by
      apply O.mem_of_valuation_le_one
      have hv1 : O.valuation ((((m : ℕ) : ↥O)) : AlgebraicClosure ℚ) = 1 := by rw [← hmu]; exact O.valuation_unit mu
      have hprod : (p : AlgebraicClosure ℚ) ^ n * z * ((m : ℕ) : AlgebraicClosure ℚ) = ((d.natAbs : ℕ) : AlgebraicClosure ℚ) * z := by
        rw [hnm]; push_cast; ring
      have hle : O.valuation (((d.natAbs : ℕ) : AlgebraicClosure ℚ) * z) ≤ 1 := O.valuation_le_one ⟨_, habs⟩
      calc O.valuation ((p : AlgebraicClosure ℚ) ^ n * z)
          = O.valuation ((p : AlgebraicClosure ℚ) ^ n * z) * O.valuation ((((m : ℕ) : ↥O)) : AlgebraicClosure ℚ) := by rw [hv1, mul_one]
        _ = O.valuation ((p : AlgebraicClosure ℚ) ^ n * z * ((m : ℕ) : AlgebraicClosure ℚ)) := by rw [← map_mul]; rfl
        _ ≤ 1 := by rw [hprod]; exact hle
    refine ⟨⟨⟨(p : AlgebraicClosure ℚ) ^ n * z, hmem⟩, ⟨((p : ℕ) : ↥O) ^ n, n, rfl⟩⟩, ?_⟩
    show z * ((((p : ℕ) : ↥O) ^ n : ↥O) : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ n * z
    push_cast
    ring
  · intro x y hxy
    exact ⟨1, by simpa using Subtype.ext hxy⟩

end S_ValuationSubring_isLocalization_away_natCast_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_isLocalization_away_natCast_of_liesOverPrime (solution)
