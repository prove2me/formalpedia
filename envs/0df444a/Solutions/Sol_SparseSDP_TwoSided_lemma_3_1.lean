-- Prove2me | solution 1 for SparseSDP.TwoSided.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:25:44.280081+00:00
-- url     : https://prove2.me/submissions/1fd57c82-c15d-49d7-a265-77244621ddbe

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_gap
import Definitions.Def_SparseSDP_TwoSided_zHat

open Matrix
open scoped Matrix.Norms.L2Operator

open SparseSDP.TwoSided in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜) (ψ : Fin n → 𝕜)
    (ω : ℝ) (hA : A.IsHermitian) (hω : ‖A‖ ≤ ω) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    ∑ i, ‖ψ i‖ ^ 2 * zEst A ψ i = RCLike.re (star ψ ⬝ᵥ (A *ᵥ ψ)) ∧
    ∑ i, ‖ψ i‖ ^ 2 * zEst A ψ i ^ 2 ≤ l2 (A *ᵥ ψ) ^ 2 ∧
    l2 (A *ᵥ ψ) ^ 2 ≤ ω ^ 2 := by
  have hl2 : l2 (A *ᵥ ψ) ^ 2 = ∑ i, ‖(A *ᵥ ψ) i‖ ^ 2 := by
    unfold l2
    exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))
  refine ⟨?_, ?_, ?_⟩
  · unfold zEst
    rw [dotProduct, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : ψ i = 0
    · simp [hi]
    · rw [← RCLike.re_ofReal_mul]
      congr 1
      rw [Pi.star_apply, RCLike.star_def]
      have h : ((‖ψ i‖ ^ 2 : ℝ) : 𝕜) = ψ i * (starRingEnd 𝕜) (ψ i) := by
        rw [RCLike.mul_conj]; push_cast; ring
      rw [h]
      field_simp
  · rw [hl2]
    refine Finset.sum_le_sum (fun i _ => ?_)
    unfold zEst
    by_cases hi : ψ i = 0
    · simp [hi]
    · have hre := RCLike.abs_re_le_norm ((A *ᵥ ψ) i / ψ i)
      have hsq : RCLike.re ((A *ᵥ ψ) i / ψ i) ^ 2 ≤ ‖(A *ᵥ ψ) i / ψ i‖ ^ 2 := by
        have := abs_nonneg (RCLike.re ((A *ᵥ ψ) i / ψ i))
        nlinarith [sq_abs (RCLike.re ((A *ᵥ ψ) i / ψ i))]
      have hn : ‖ψ i‖ ≠ 0 := norm_ne_zero_iff.mpr hi
      calc ‖ψ i‖ ^ 2 * RCLike.re ((A *ᵥ ψ) i / ψ i) ^ 2
          ≤ ‖ψ i‖ ^ 2 * ‖(A *ᵥ ψ) i / ψ i‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = ‖(A *ᵥ ψ) i‖ ^ 2 := by
            rw [norm_div]
            field_simp
  · have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 ψ)
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
    simp only [WithLp.ofLp_toLp, hψ, Real.sqrt_one, mul_one] at h
    have h' : l2 (A *ᵥ ψ) ≤ ω := by
      refine le_trans ?_ (h.trans hω)
      unfold l2
      exact le_of_eq rfl
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h' 2
