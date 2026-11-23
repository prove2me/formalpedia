-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_re_U
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:09.674478+00:00
-- url     : https://prove2.me/submissions/0b187d14-2e2c-45a6-a77b-57572090667c

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
theorem _root_.solution (q : ℕ) {n : ℕ} (v a : Fin n → Vsp X.dim) :
    ((q : ℂ) * Real.pi * HC v a - q * Real.pi * HC a a / 2).re =
      q * Real.pi * (HC v a).re - q * Real.pi * (HC a a).re / 2 := by
  simp [Complex.mul_re, Complex.sub_re]
end ReciprocityTheory.ChartRestriction.G.I2
