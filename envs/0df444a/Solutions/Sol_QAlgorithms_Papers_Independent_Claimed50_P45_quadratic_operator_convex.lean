-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P45.quadratic_operator_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:46:38.913889+00:00
-- url     : https://prove2.me/submissions/87538324-e1c1-403e-a2ad-457b28be51c6

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P45
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P45

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter Topology QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)

open QAlgorithms.Papers.Independent.Dependency50.P28
  (LE pinch logNonnegativeExtended typeI accept scaled TestSequence)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I]


/-- PDF p.11, Lemma 5, (62)–(63): Loewner convexity of X ↦ X* A X on
ALL complex matrices, with a positive semidefinite A and real t in [0,1].
Neither normalization of A nor Hermiticity of X or Y is assumed. -/
theorem solution
    (A : Mat I) (hA : A.PosSemidef) (X Y : Mat I)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    LE (((t : ℂ) • X + ((1 - t : ℝ) : ℂ) • Y)ᴴ * A *
          ((t : ℂ) • X + ((1 - t : ℝ) : ℂ) • Y))
      ((t : ℂ) • (Xᴴ * A * X) + ((1 - t : ℝ) : ℂ) • (Yᴴ * A * Y)) := by
  unfold QAlgorithms.Papers.Independent.Dependency50.P28.LE
  set s : ℂ := (t : ℂ)
  have hu : (((1 - t : ℝ)) : ℂ) = 1 - s := by push_cast; rfl
  have hs : star s = s := by simp [s]
  rw [hu]
  have key : (s • (Xᴴ * A * X) + (1 - s) • (Yᴴ * A * Y)) -
      (s • X + (1 - s) • Y)ᴴ * A * (s • X + (1 - s) • Y) =
      (s * (1 - s)) • ((X - Y)ᴴ * A * (X - Y)) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, star_sub,
      star_one, hs, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.mul_sub, smul_smul]
    module
  rw [key]
  apply Matrix.PosSemidef.smul (hA.conjTranspose_mul_mul_same (X - Y))
  have h1 : (0 : ℝ) ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
  have : s * (1 - s) = ((t * (1 - t) : ℝ) : ℂ) := by push_cast; rfl
  rw [this]; exact_mod_cast h1



end
