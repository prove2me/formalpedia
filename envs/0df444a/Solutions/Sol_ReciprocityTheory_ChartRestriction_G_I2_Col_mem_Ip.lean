-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.mem_Ip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:14:11.679171+00:00
-- url     : https://prove2.me/submissions/d7cc7ded-8a20-4497-bba6-66ba0f9cc406

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
variable (X : PT E) (I : Submodule ℤ (Vsp X.dim))
namespace ReciprocityTheory.ChartRestriction.G.I2.Col
theorem _root_.solution {x : Vsp X.dim} : x ∈ Ip X I ↔ x ∈ X.L ∧ ∀ a ∈ I, (Hf x a).im = 0 := Iff.rfl
end ReciprocityTheory.ChartRestriction.G.I2.Col
