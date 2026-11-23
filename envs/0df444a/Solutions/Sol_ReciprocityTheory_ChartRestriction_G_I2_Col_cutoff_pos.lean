-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.cutoff_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:24:35.402377+00:00
-- url     : https://prove2.me/submissions/37efa07e-79f5-4c37-8cd7-411ccb2d3de3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_MemOfProjTwoEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex NumberField
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {E : Type} [Field E] [NumberField E]
variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF}
namespace ReciprocityTheory.ChartRestriction.G.I2.Col
theorem _root_.solution (P : Par X DF) : 0 < b0 (E := E) P.q P.R0 := by
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hRR : 0 < RR (E := E) := by simp only [RR]; have := P.hrd; positivity
  have hR0 := P.hR0.1
  have : 0 < P.R0 ^ 2 := by linarith
  simp only [b0]; positivity
end ReciprocityTheory.ChartRestriction.G.I2.Col
