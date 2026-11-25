-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.threshold_le_firstMinimum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:32:46.70212+00:00
-- url     : https://prove2.me/submissions/248ceede-441c-487c-89cb-4b52e85c7a07

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_f_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_firstMinimum_pos_bis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (h0 : P.ph = 0) :
    th (E := E) P.q P.R0 ≤ X.la1 := by
  by_contra hlt
  push_neg at hlt
  have hp : P.ph = 2 * PT.f E / (PT.rd E ^ 2 * X.la1 ^ 2) := by
    simp only [Par.ph, PT.ph, if_pos hlt]
  rw [hp] at h0
  have hla := firstMinimum_pos_bis P
  have hf : (1 : ℝ) ≤ PT.f E := by exact_mod_cast f_pos P
  have hrd : (16 : ℝ) ≤ PT.rd E := P.hrd
  have hpos : 0 < 2 * (PT.f E : ℝ) / (PT.rd E ^ 2 * X.la1 ^ 2) :=
    div_pos (by linarith) (mul_pos (pow_pos (by linarith) 2) (pow_pos hla 2))
  linarith
end ReciprocityTheory.ChartRestriction.G.I2
