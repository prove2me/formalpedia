-- Prove2me | solution 1 for PI.PhMeasCore.UnitaryGroupMassFormula.mul_mem_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:37.254043+00:00
-- url     : https://prove2.me/submissions/42f74fbc-78ad-4223-889a-84bffad2bf43

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_ContDiffMulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open PI PI.PhMeasCore PI.PhMeasCore.UnitaryGroupMassFormula
open PI.PhMeasCore
namespace PI.PhMeasCore.UnitaryGroupMassFormula
theorem _root_.solution {n : ℕ} {Hm a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UH Hm) (hb : b ∈ UH Hm) :
    a * b ∈ UH Hm := by
  have ha' : aᴴ * Hm * a = Hm := ha
  have hb' : bᴴ * Hm * b = Hm := hb
  show (a * b)ᴴ * Hm * (a * b) = Hm
  calc (a * b)ᴴ * Hm * (a * b) = bᴴ * (aᴴ * Hm * a) * b := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Hm := by rw [ha', hb']
end PI.PhMeasCore.UnitaryGroupMassFormula
