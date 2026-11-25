-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ctU_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:10:27.721174+00:00
-- url     : https://prove2.me/submissions/9ff5d30f-2dcf-49cf-923d-9aee7a9b0ef2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
private theorem Hf_sub_leftSquareIntegrability (a b c : EuclideanSpace ℂ ι) : Hf (a - b) c = Hf a c - Hf b c := by
  simp [Hf, sub_mul, Finset.sum_sub_distrib]
private theorem Hf_neg_left' (a c : EuclideanSpace ℂ ι) : Hf (-a) c = -Hf a c := by
  simp [Hf, Finset.sum_neg_distrib]
private theorem Hf_neg_right' (a c : EuclideanSpace ℂ ι) : Hf a (-c) = -Hf a c := by
  simp [Hf, Finset.sum_neg_distrib]
end
end ReciprocityTheory.ChartRestriction.G.I2
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
variable {K : Submodule ℝ (EuclideanSpace ℂ ι)} (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
include hK
end
end ReciprocityTheory.ChartRestriction.G.I2
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (q : ℕ) (b : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) :
    ctU q b (ctU q (-b) F) = F := by
  funext t
  have e : (q * Real.pi * Hf t b - q * Real.pi * Hf b b / 2 : ℂ) +
      (q * Real.pi * Hf (t - b) (-b) - q * Real.pi * Hf (-b) (-b) / 2) = 0 := by
    simp only [Hf_sub_leftSquareIntegrability, Hf_neg_right', Hf_neg_left', neg_neg]
    ring
  simp only [ctU]
  rw [← mul_assoc, ← Complex.exp_add, e, Complex.exp_zero, one_mul, sub_neg_eq_add, sub_add_cancel]
end ReciprocityTheory.ChartRestriction.G.I2
