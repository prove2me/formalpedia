-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.lemS_detM_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:30:48.203449+00:00
-- url     : https://prove2.me/submissions/79b5ec81-4dd1-4257-bb16-70f0120589be

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemSJ_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemSG_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemSG_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
open scoped Matrix
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (Y : GT ι) (b₀ : OrthonormalBasis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι)) :
    |b₀.toBasis.det Y.b| ≤ 1 := by
  obtain ⟨C, hC⟩ := lemSG_inv Y
  have hdet := congrArg Matrix.det hC
  rw [Matrix.det_mul, Matrix.det_one, lemSG_det Y.b b₀, ← Int.cast_det] at hdet
  have hJ := lemSJ_det (ι := ι)
  have hC0 : C.det ≠ 0 := by
    rintro h
    rw [h] at hdet
    simp at hdet
  have h1 : (1 : ℝ) ≤ |(C.det : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hC0
  have habs := congrArg abs hdet
  simp only [abs_mul, abs_one, hJ, one_mul] at habs
  nlinarith [abs_nonneg (b₀.toBasis.det Y.b), mul_nonneg (sub_nonneg.2 h1)
    (mul_self_nonneg |b₀.toBasis.det Y.b|)]
end ReciprocityTheory.ChartRestriction.G.I2
