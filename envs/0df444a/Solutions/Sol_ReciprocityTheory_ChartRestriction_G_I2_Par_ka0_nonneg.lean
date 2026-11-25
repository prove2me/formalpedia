-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Par_ka0_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:39:58.733419+00:00
-- url     : https://prove2.me/submissions/dad846e0-93d9-4a16-9e6d-7131348d814d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofUMapSqSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {X : PT E} {DF : ℕ} (P : Par X DF) : 0 ≤ P.ka0 := by
  have h : (0 : ℝ) ≤ PT.rd E := by linarith [P.hrd]
  have hR : (0 : ℝ) ≤ RR (E := E) := by
    unfold RR
    exact pow_nonneg h 7
  unfold Par.ka0
  exact mul_nonneg (mul_nonneg (by norm_num) hR) (sq_nonneg _)
end ReciprocityTheory.ChartRestriction.G.I2
