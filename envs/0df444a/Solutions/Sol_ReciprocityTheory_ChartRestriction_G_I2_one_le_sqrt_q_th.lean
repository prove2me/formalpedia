-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.one_le_sqrt_q_th
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:08:10.814125+00:00
-- url     : https://prove2.me/submissions/f568d9df-93f2-41d0-9281-9cbdedbe1055

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_f_pos

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
theorem _root_.solution {X : PT E} {DF : ℕ} (P : Par X DF) :
    1 ≤ Real.sqrt P.q * th (E := E) P.q P.R0 := by
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hf : (1 : ℝ) ≤ PT.f E := by exact_mod_cast f_pos P
  have hR : (270 : ℝ) ≤ P.R0 ^ 2 := P.hR0.1
  have hrd : (16 : ℝ) ≤ PT.rd E := P.hrd
  have hRR : 1 ≤ RR (E := E) := by
    unfold RR
    exact one_le_pow₀ (by linarith)
  have h3 : 1 ≤ RR (E := E) ^ 3 := one_le_pow₀ hRR
  unfold th
  rw [← Real.sqrt_mul hq.le]
  have hA : (P.q : ℝ) * (PT.f E * P.R0 ^ 2 * RR (E := E) ^ 3 / P.q) =
      PT.f E * P.R0 ^ 2 * RR (E := E) ^ 3 := by
    field_simp
  rw [hA, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  apply Real.sqrt_le_sqrt
  have h1 : (270 : ℝ) ≤ PT.f E * P.R0 ^ 2 := by nlinarith
  nlinarith
end ReciprocityTheory.ChartRestriction.G.I2
