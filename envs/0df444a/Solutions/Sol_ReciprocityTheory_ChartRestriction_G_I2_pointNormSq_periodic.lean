-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.pointNormSq_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:12:47.477831+00:00
-- url     : https://prove2.me/submissions/558b6301-2b59-429d-8f1b-af8783b8f961

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
private theorem Hf_add_left_euclidean (a b c : EuclideanSpace ℂ ι) : Hf (a + b) c = Hf a c + Hf b c := by
  simp [Hf, add_mul, Finset.sum_add_distrib]
private theorem Hf_add_right_euclidean (a b c : EuclideanSpace ℂ ι) : Hf a (b + c) = Hf a b + Hf a c := by
  simp [Hf, mul_add, Finset.sum_add_distrib]
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
theorem _root_.solution (Y : GT ι) {q : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec q)
    {γ : EuclideanSpace ℂ ι} (hγ : γ ∈ lat Y.b) (t : EuclideanSpace ℂ ι) :
    Y.ptN2 q F (t + γ) = Y.ptN2 q F t := by
  obtain ⟨_, hFe⟩ := hF
  have e1 : ‖t + γ‖ ^ 2 = ‖t‖ ^ 2 + 2 * (Hf t γ).re + ‖γ‖ ^ 2 := by
    rw [norm_sq_eq_re_Hf_self (t + γ), norm_sq_eq_re_Hf_self t, norm_sq_eq_re_Hf_self γ, Hf_add_left_euclidean, Hf_add_right_euclidean, Hf_add_right_euclidean,
      Hf_swap_eq_conj' t γ]
    simp only [Complex.add_re, Complex.conj_re]
    ring
  have hA : ((q : ℂ) * (Real.pi : ℂ) * Hf t γ + (q : ℂ) * (Real.pi : ℂ) * Hf γ γ / 2) =
      ((q * Real.pi : ℝ) : ℂ) * Hf t γ + ((q * Real.pi / 2 : ℝ) : ℂ) * Hf γ γ := by
    push_cast
    ring
  simp only [GT.ptN2]
  rw [hFe γ hγ t, hA, norm_mul, norm_mul, Y.ka_abs γ hγ, one_mul, Complex.norm_exp, Complex.add_re,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul, ← norm_sq_eq_re_Hf_self γ, e1]
  rw [mul_pow, mul_comm (Real.exp _ ^ 2), mul_assoc]
  congr 1
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring
end ReciprocityTheory.ChartRestriction.G.I2
