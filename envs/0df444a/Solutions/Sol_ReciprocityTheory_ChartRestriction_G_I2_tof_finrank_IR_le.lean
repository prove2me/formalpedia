-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.tof_finrank_IR_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:32:29.456624+00:00
-- url     : https://prove2.me/submissions/1056d4c3-bf29-414b-9ed3-f470e271de91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofFinrankIRLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


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
theorem _root_.solution [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) : Module.finrank ℝ (IR I) ≤ dstar (E := E) P.m := by
  obtain ⟨ρ, hρ, h⟩ := hI.rank
  rw [h]
  unfold dstar
  exact Nat.mul_le_mul_left _ hρ
end ReciprocityTheory.ChartRestriction.G.I2
