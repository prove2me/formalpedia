-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitDivVertical_proof_66147d14edd8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:07:44.90437+00:00
-- url     : https://prove2.me/submissions/3204b8a1-bfa9-4b80-b515-9841ba7b8c36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDivVertical
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_int_poly_coeff_zero_ne_zero_3cecf393ad2e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mConeMap_of_isMultiHomog_f3a1bcb1fd3a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
namespace GroundTheory.Heights₂.Heights
namespace OrbitDivVertical
theorem _root_.solution : OrbitDivVertical.Statement := by
  intro ι _ _ _ n A x s _ hs V hV hH
  obtain ⟨a, -, hsa, hsW⟩ := hs
  obtain ⟨hVmin, hVrel⟩ := hV
  have hVp : V.IsPrime := hVmin.1.1
  have hWV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  have hsV : s ∈ V := hVmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  choose c hc using hVrel
  set M : MvPolynomial (Coord n) ℤ := chartMonomial c a with hMdef
  have hMV : M ∉ V := by
    rw [hMdef, chartMonomial]
    intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hVp)).mp h
    exact hc k (hVp.mem_of_pow_mem _ hk)
  have hMa : Geo.IsMultiHomog (ι := blockIdx n) M a :=
    (geoMultiHomog_iff _ a).mpr (isWeightedHomogeneous_chartMonomial c a)
  set y := flatCone x
  set T : MvPolynomial ι (AlgebraicClosure ℚ) := ∏ k, X k ^ a k
  set σ := eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) y s
  set μ := eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) y M
  have hφs : Geo.mConeMap (ι := blockIdx n) y s = C σ * T := mConeMap_of_isMultiHomog y s a hsa
  have hφM : Geo.mConeMap (ι := blockIdx n) y M = C μ * T := mConeMap_of_isMultiHomog y M a hMa
  have hσ : σ ≠ 0 := fun h ↦ hsW (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, hφs, h, map_zero, zero_mul])
  have hμ : μ ≠ 0 := fun h ↦ hMV (hWV (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, hφM, h, map_zero, zero_mul]))
  obtain ⟨P, hP0, hP⟩ := exists_int_poly_coeff_zero_ne_zero (div_ne_zero hσ hμ)
  set m := P.natDegree
  let f : ℕ → MvPolynomial (Coord n) ℤ := fun j ↦ C (P.coeff j) * s ^ j * M ^ (m - j)
  have hfW : ∑ j ∈ Finset.range (m + 1), f j ∈ orbitIdeal x := by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, map_sum]
    have hterm : ∀ j ∈ Finset.range (m + 1), Geo.mConeMap (ι := blockIdx n) y (f j) =
        C (algebraMap ℤ (AlgebraicClosure ℚ) (P.coeff j) * (σ / μ) ^ j * μ ^ m) * T ^ m := by
      intro j hj
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have e1 : (σ / μ) ^ j * μ ^ m = σ ^ j * μ ^ (m - j) := by
        rw [← Nat.add_sub_cancel' hjm, pow_add, Nat.add_sub_cancel_left, div_pow, ← mul_assoc,
          div_mul_cancel₀ _ (pow_ne_zero _ hμ)]
      have e2 : T ^ m = T ^ j * T ^ (m - j) := by rw [← pow_add, Nat.add_sub_cancel' hjm]
      simp only [f, map_mul, map_pow, hφs, hφM, MvPolynomial.algHom_C, mul_assoc, e1, e2]
      simp only [eq_intCast, map_intCast, mul_pow]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum, ← Finset.sum_mul]
    have hPτ : ∑ j ∈ Finset.range (m + 1), algebraMap ℤ (AlgebraicClosure ℚ) (P.coeff j) *
        (σ / μ) ^ j = 0 := by
      rw [← hP, Polynomial.aeval_eq_sum_range]
      simp [Algebra.smul_def]
      rfl
    rw [hPτ, zero_mul, map_zero, zero_mul]
  have hrest : ∑ j ∈ Finset.range m, f (j + 1) ∈ V :=
    Ideal.sum_mem _ fun j _ ↦ by
      simp only [f]
      rw [pow_succ]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hsV))
  have h0 : f 0 ∈ V := by
    have h := Ideal.sub_mem V (hWV hfW) hrest
    rwa [Finset.sum_range_succ', add_sub_cancel_left] at h
  simp only [f, pow_zero, mul_one, Nat.sub_zero] at h0
  rcases hVp.mem_or_mem h0 with hC | hM
  · apply hP0
    have : P.coeff 0 ∈ V.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := hC
    rw [show V.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) = ⊥ from hH] at this
    exact (Ideal.mem_bot).mp this
  · exact hMV (hVp.mem_of_pow_mem _ hM)
end OrbitDivVertical
end GroundTheory.Heights₂.Heights
