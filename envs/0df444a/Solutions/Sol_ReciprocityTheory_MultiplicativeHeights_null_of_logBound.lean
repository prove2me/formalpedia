-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.null_of_logBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:36:46.635784+00:00
-- url     : https://prove2.me/submissions/6bdb258f-10d1-4d2d-b94e-5a62313013af

import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockSphereMeasure_isProbability
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurable_eval_blockCoords
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_isMultiHomogeneous_C_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {B n : ℕ} (hn : 0 < n) (hInt : SphereLogIntegrableStatement)
    (hbound : ∀ (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ) (u : BlockSphere B n),
      IsMultiHomogeneous a g → eval (blockPoint u) g ≠ 0 →
      Real.log ‖eval (blockPoint u) g‖ - (∑ b, (a b : ℝ)) / 2 * (harmonic (n - 1) : ℝ) ≤
        blockSphereMean B n g)
    (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ) (u : BlockSphere B n)
    (hg : IsMultiHomogeneous a g) (hu : eval (blockPoint u) g ≠ 0) :
    blockSphereProb B n {z | eval (blockPoint z) g = 0} = 0 := by
  classical
  haveI := blockSphereMeasure_isProbability (B := B) hn
  have hZm : MeasurableSet {z : BlockSphere B n | eval (blockPoint z) g = 0} :=
    measurableSet_eq_fun (measurable_eval_blockCoords g) measurable_const
  have hg0 : g ≠ 0 := by rintro rfl; exact hu (by simp)
  have hI := hInt B n a g hg0 hg
  have hmean : ∀ c : ℂ, c ≠ 0 → blockSphereMean B n (C c * g) = blockSphereMean B n g +
      (blockSphereProb B n).real {z | eval (blockPoint z) g = 0}ᶜ * Real.log ‖c‖ := by
    intro c hc
    have hpt : (fun z => Real.log ‖eval (blockPoint z) (C c * g)‖) = fun z =>
        Real.log ‖eval (blockPoint z) g‖ +
          {z : BlockSphere B n | eval (blockPoint z) g = 0}ᶜ.indicator (fun _ => Real.log ‖c‖) z := by
      funext z
      by_cases hz : eval (blockPoint z) g = 0
      · have hz' : z ∉ {z : BlockSphere B n | eval (blockPoint z) g = 0}ᶜ := fun h => h hz
        rw [Set.indicator_of_notMem hz', map_mul, hz, mul_zero, add_zero]
      · have hz' : z ∈ {z : BlockSphere B n | eval (blockPoint z) g = 0}ᶜ := hz
        rw [Set.indicator_of_mem hz', map_mul, eval_C, norm_mul,
          Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hz)]
        ring
    unfold blockSphereMean
    rw [hpt, integral_add hI ((integrable_const _).indicator hZm.compl),
      integral_indicator_const _ hZm.compl, smul_eq_mul]
  by_contra hne
  have hP : 0 < (blockSphereProb B n).real {z | eval (blockPoint z) g = 0} :=
    ENNReal.toReal_pos hne (measure_ne_top _ _)
  have hcompl : (blockSphereProb B n).real {z | eval (blockPoint z) g = 0}ᶜ =
      1 - (blockSphereProb B n).real {z | eval (blockPoint z) g = 0} := by
    simp only [Measure.real]
    rw [prob_compl_eq_one_sub hZm, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  set P := (blockSphereProb B n).real {z | eval (blockPoint z) g = 0} with hPdef
  set M : ℝ := blockSphereMean B n g - Real.log ‖eval (blockPoint u) g‖ +
    (∑ b, (a b : ℝ)) / 2 * (harmonic (n - 1) : ℝ) with hM
  set c : ℂ := ((Real.exp ((M + 1) / P) : ℝ) : ℂ) with hcdef
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hlc : Real.log ‖c‖ = (M + 1) / P := by
    rw [hcdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.log_exp]
  have hb := hbound a (C c * g) u (isMultiHomogeneous_C_mul hg c)
    (by rw [map_mul, eval_C]; exact mul_ne_zero hc hu)
  rw [hmean c hc, hcompl, map_mul, eval_C, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hu), hlc] at hb
  have h1 : P * ((M + 1) / P) = M + 1 := by field_simp
  have h2 : (1 - P) * ((M + 1) / P) = (M + 1) / P - (M + 1) := by rw [sub_mul, one_mul, h1]
  rw [h2] at hb
  linarith
end ReciprocityTheory.MultiplicativeHeights
