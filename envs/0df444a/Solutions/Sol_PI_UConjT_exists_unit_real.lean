-- Prove2me | solution 1 for PI.UConjT.exists_unit_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:32:03.569859+00:00
-- url     : https://prove2.me/submissions/26266521-c9d6-4cc3-8778-31ef01786978

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_TransferStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_ExistsUnitReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UConjT
open ComplexConjugate
namespace PI.UConjT
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (w e : E) (hw : w ≠ 0) :
    ∃ c : ℂ, ‖c • w‖ = 1 ∧ (inner ℂ (c • w) e).im = 0 := by
  set z : ℂ := inner ℂ w e with hzdef
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  by_cases hz : z = 0
  · refine ⟨((‖w‖⁻¹ : ℝ) : ℂ), ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      field_simp
    · rw [inner_smul_left, ← hzdef, hz]; simp
  · have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    refine ⟨z * ((‖z‖⁻¹ * ‖w‖⁻¹ : ℝ) : ℂ), ?_, ?_⟩
    · rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      field_simp
    · rw [inner_smul_left, ← hzdef]
      simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, map_mul]
      ring
end PI.UConjT
