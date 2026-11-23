-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.th_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:28.938871+00:00
-- url     : https://prove2.me/submissions/b8fef90f-3b59-446b-a26e-dd926db13542

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
theorem _root_.solution (P : Par X DF) : 0 < P.th := by
  have hf : (1 : ℝ) ≤ PT.f E := by
    have := P.hfr
    have : 1 ≤ PT.f E := by
      rcases Nat.eq_zero_or_pos (PT.f E) with h | h
      · rw [h] at this; simp at this
      · exact h
    exact_mod_cast this
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hRR : 0 < RR (E := E) := by simp only [RR]; have := P.hrd; positivity
  have hR0 := P.hR0.1
  simp only [Par.th, th]
  apply Real.sqrt_pos.2
  apply div_pos _ hq
  have : 0 < P.R0 ^ 2 := by linarith
  positivity
end ReciprocityTheory.ChartRestriction.G.I2.Col
