-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.detM_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:31:27.666806+00:00
-- url     : https://prove2.me/submissions/59b85dbb-c395-44e1-8d5f-dc875a0e5af3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_DetMEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemSG_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemSG_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemSJ_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution (Y : GT ι) (b₀ : OrthonormalBasis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι)) :
    |b₀.toBasis.det Y.b| = 1 := by
  have hM : ∀ i k, ∃ m : ℤ, (Hf (Y.b i) (Y.b k)).im = m := fun i k =>
    Y.integral _ _ (Submodule.subset_span ⟨i, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  choose m hm using hM
  have hG : lemSG Y.b = (Matrix.of m).map (Int.cast : ℤ → ℝ) := by
    ext i k; simp [lemSG, hm]
  obtain ⟨C, hC⟩ := lemSG_inv Y
  have h1 := congrArg Matrix.det hC
  rw [Matrix.det_mul, Matrix.det_one] at h1
  have h2 := h1
  rw [hG, ← Int.cast_det, ← Int.cast_det] at h2
  have h3 : C.det * (Matrix.of m).det = 1 := by exact_mod_cast h2
  have h4 : |(Matrix.of m).det| = 1 := by
    have h3' : (Matrix.of m).det * C.det = 1 := by rw [mul_comm]; exact h3
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h3' with h | h <;> rw [h] <;> rfl
  have h5 : |(lemSG Y.b).det| = 1 := by
    rw [hG, ← Int.cast_det, ← Int.cast_abs, h4, Int.cast_one]
  rw [lemSG_det Y.b b₀, abs_mul, abs_mul, lemSJ_det, one_mul] at h5
  have hd := abs_nonneg (b₀.toBasis.det Y.b)
  nlinarith
end ReciprocityTheory.ChartRestriction.G.I2.FPw
