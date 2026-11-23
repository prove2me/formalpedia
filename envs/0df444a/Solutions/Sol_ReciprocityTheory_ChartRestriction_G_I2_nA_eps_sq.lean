-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_eps_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:01.911066+00:00
-- url     : https://prove2.me/submissions/fa702d44-732c-412c-9e8e-b87e12a725ba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E] (X : PT E)
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {x : Vsp X.dim} (hx : x ∈ X.L) : ((X.eps x : ℂ)) ^ 2 = 1 := by
  rcases X.eps_pm x hx with h | h <;> simp [h]
end ReciprocityTheory.ChartRestriction.G.I2
