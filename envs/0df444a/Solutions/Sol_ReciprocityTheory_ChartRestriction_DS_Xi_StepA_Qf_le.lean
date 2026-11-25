-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Qf_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:21.137193+00:00
-- url     : https://prove2.me/submissions/a8faa029-7623-42f3-8f10-31906600edca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergFactsOfInductiveInput
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InnerCLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_mw_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (A C0 : ℝ)
    (hC0 : ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r', EInt k r' A c g ≤ ENNReal.ofReal (C0 * mw k r' c *
        gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)))
    (s1 : Fin (r' + 1) → ℝ) (μ₁ : Measure (Mt k r')) (hμ₁ : IsHaarOn (GV k r') μ₁) (c : ℂ) (hc : c ≠ 0) :
    Qf k r' A s1 μ₁ c ≤
      ENNReal.ofReal (|C0| * mw k r' c) * JInt μ₁ (A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) s1 := by
  unfold Qf JInt
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  have hconc : ∀ᵐ g ∂μ₁, Matrix.of g ∈ GV k r' := by rw [ae_iff]; exact hμ₁.conc
  filter_upwards [hconc] with g hg
  rw [← mul_assoc]
  gcongr ?_ * _
  refine (hC0 c hc _ hg).trans ?_
  have hG : 0 ≤ gN (Matrix.of g) ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A) :=
    Real.rpow_nonneg (by unfold gN; exact Real.sqrt_nonneg _) _
  rw [← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (mw_nonneg k r' c)),
    show -(A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) = ((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A by ring]
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (mw_nonneg k r' c)) hG
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
