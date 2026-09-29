-- Prove2me | solution 1 for RobustSDP.Uniqueness.trace_RtRZ_pos
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:06:29.33797+00:00
-- url     : https://prove2.me/submissions/257e19d0-fb43-4488-88ab-219529edc179

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix

namespace RobustSDP.Uniqueness

theorem aux_trpos_key {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosSemidef) :
    0 ≤ (Aᵀ * A * Z).trace ∧ ((Aᵀ * A * Z).trace = 0 → A * Z = 0) := by
  have htr : (Aᵀ * A * Z).trace = (A * Z * Aᴴ).trace := by
    rw [conjTranspose_eq_transpose_of_trivial, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  have hP : (A * Z * Aᴴ).PosSemidef := hZ.mul_mul_conjTranspose_same A
  refine ⟨htr ▸ hP.trace_nonneg, fun h0 => ?_⟩
  rw [htr, hP.trace_eq_zero_iff, conjTranspose_eq_transpose_of_trivial] at h0
  have hvec : ∀ v : Fin k → ℝ, Z *ᵥ (Aᵀ *ᵥ v) = 0 := by
    intro v
    rw [← hZ.dotProduct_mulVec_zero_iff]
    have h1 : v ⬝ᵥ (A * Z * Aᵀ) *ᵥ v = 0 := by rw [h0]; simp
    rw [star_trivial]
    rw [← h1, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec v A, ← mulVec_transpose]
  have hZA : Z * Aᵀ = 0 := by
    ext i j
    have := congrFun (hvec (Pi.single j 1)) i
    rw [mulVec_mulVec, mulVec_single_one] at this
    exact this
  have hZt : Zᵀ = Z := by
    have := hZ.isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have := congrArg Matrix.transpose hZA
  rwa [transpose_mul, transpose_transpose, hZt, transpose_zero] at this

end RobustSDP.Uniqueness

open RobustSDP.Uniqueness

theorem solution {m n p q : ℕ} (D : SDPData m n p q) (h3b : D.H3b)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosSemidef) (hZ0 : Z ≠ 0)
    (x : Fin m → ℝ) (τ : ℝ) (hτ : τ ≠ 0) :
    ¬ ((D.L * D.Lᵀ * Z).trace = 0 ∧ ((D.R x)ᵀ * D.R x * Z).trace = 0) ∧
      (τ ^ 2 * (D.L * D.Lᵀ * Z).trace = ((D.R x)ᵀ * D.R x * Z).trace →
        0 < ((D.R x)ᵀ * D.R x * Z).trace) := by
  have kL := aux_trpos_key D.Lᵀ Z hZ
  rw [transpose_transpose] at kL
  have kR := aux_trpos_key (D.R x) Z hZ
  have part1 : ¬ ((D.L * D.Lᵀ * Z).trace = 0 ∧ ((D.R x)ᵀ * D.R x * Z).trace = 0) := by
    rintro ⟨h1, h2⟩
    have eL := kL.2 h1
    have eR := kR.2 h2
    apply hZ0
    ext i j
    have hinj := h3b x
    have hw : (Matrix.fromRows D.Lᵀ (D.R x)) *ᵥ (fun a => Z a j) =
        (Matrix.fromRows D.Lᵀ (D.R x)) *ᵥ 0 := by
      rw [fromRows_mulVec, fromRows_mulVec, mulVec_zero, mulVec_zero]
      congr 1
      · funext a
        have := congrFun (congrFun eL a) j
        simpa [mul_apply, mulVec, dotProduct] using this
      · funext a
        have := congrFun (congrFun eR a) j
        simpa [mul_apply, mulVec, dotProduct] using this
    have := congrFun (hinj hw) i
    simpa using this
  refine ⟨part1, fun h => ?_⟩
  rcases kR.1.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    apply part1
    refine ⟨?_, heq.symm⟩
    rw [← heq] at h
    have hτ2 : τ ^ 2 ≠ 0 := pow_ne_zero 2 hτ
    exact (mul_eq_zero.mp h).resolve_left hτ2
