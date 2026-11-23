-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.pointNormSq_translate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:02:30.626967+00:00
-- url     : https://prove2.me/submissions/c6bdc661-02ef-4889-9a16-b0f8e1c088e0

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
private theorem Hf_sub_right' (a b c : EuclideanSpace ℂ ι) : Hf a (b - c) = Hf a b - Hf a c := by
  simp [Hf, mul_sub, Finset.sum_sub_distrib]
private theorem Hf_swap_eq_conj' (a b : EuclideanSpace ℂ ι) : Hf b a = (starRingEnd ℂ) (Hf a b) := by
  simp only [Hf, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
private theorem norm_sq_eq_re_Hf_self (v : EuclideanSpace ℂ ι) : ‖v‖ ^ 2 = (Hf v v).re := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [Hf, Complex.re_sum, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  all_goals rfl
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
theorem _root_.solution (Y : GT ι) (q : ℕ) (b : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ)
    (t : EuclideanSpace ℂ ι) : Y.ptN2 q (ctU q b F) t = Y.ptN2 q F (t - b) := by
  have e1 : ‖t - b‖ ^ 2 = ‖t‖ ^ 2 - 2 * (Hf t b).re + ‖b‖ ^ 2 := by
    rw [norm_sq_eq_re_Hf_self (t - b), norm_sq_eq_re_Hf_self t, norm_sq_eq_re_Hf_self b, Hf_sub_leftSquareIntegrability, Hf_sub_right', Hf_sub_right',
      Hf_swap_eq_conj' t b]
    simp only [Complex.sub_re, Complex.conj_re]
    ring
  have hA : ((q : ℂ) * (Real.pi : ℂ) * Hf t b - (q : ℂ) * (Real.pi : ℂ) * Hf b b / 2) =
      ((q * Real.pi : ℝ) : ℂ) * Hf t b - ((q * Real.pi / 2 : ℝ) : ℂ) * Hf b b := by
    push_cast
    ring
  simp only [GT.ptN2, ctU]
  rw [hA, norm_mul, Complex.norm_exp, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    ← norm_sq_eq_re_Hf_self b, e1]
  rw [mul_pow, mul_comm (Real.exp _ ^ 2), mul_assoc]
  congr 1
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring
end ReciprocityTheory.ChartRestriction.G.I2
