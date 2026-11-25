-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.src_null
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:44:26.904566+00:00
-- url     : https://prove2.me/submissions/b1b9e7c3-2194-4ba5-81b5-ea2d523e5fa6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_meas_wD
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_wD_zero_off

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
open PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.ZetaZeros
theorem _root_.solution (hD : WbData k r z z' μW μW' a a' μsec) : srcM k r z z' μW μW' (goodS k r z z')ᶜ = 0 := by
  have := hD.haarW.1
  have := hD.haarW'.1
  have h1 : (volume : Measure ℂ).withDensity (wD k r z z')
      {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ}ᶜ = 0 := by
    rw [withDensity_apply_eq_zero' meas_wD.aemeasurable]
    exact measure_mono_null (fun ζ hζ => (hζ.1 (wD_zero_off hζ.2)).elim) measure_empty
  have hsub : (goodS k r z z')ᶜ ⊆
      ({ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ}ᶜ ×ˢ Set.univ) ∪
        (Set.univ ×ˢ ({x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ)) ∪
        (Set.univ ×ˢ (Set.univ ×ˢ {x : Mt k r | Matrix.of x ∉ UWset k r z'})) := by
    intro q hq
    simp only [goodS, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or] at hq
    rcases hq with h | h | h
    · exact Or.inl (Or.inl ⟨h, trivial⟩)
    · exact Or.inl (Or.inr ⟨trivial, h, trivial⟩)
    · exact Or.inr ⟨trivial, trivial, h⟩
  refine measure_mono_null hsub (measure_union_null (measure_union_null ?_ ?_) ?_)
  · rw [srcM, Measure.prod_prod, h1, zero_mul]
  · rw [srcM, Measure.prod_prod, Measure.prod_prod, hD.haarW.2.2.1, zero_mul, mul_zero]
  · rw [srcM, Measure.prod_prod, Measure.prod_prod, hD.haarW'.2.2.1, mul_zero, mul_zero]
end PI.RhsWLim.W.ZetaZeros
