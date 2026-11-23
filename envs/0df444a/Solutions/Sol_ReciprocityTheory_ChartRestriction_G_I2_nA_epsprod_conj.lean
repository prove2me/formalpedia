-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_epsprod_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:04.917478+00:00
-- url     : https://prove2.me/submissions/c413989c-e66e-4215-83ba-e2177795559f

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
theorem _root_.solution {n : ℕ} (γ : Fin n → Vsp X.dim) :
    (starRingEnd ℂ) (∏ k, (X.eps (γ k) : ℂ)) = ∏ k, (X.eps (γ k) : ℂ) := by
  rw [map_prod]; simp
end ReciprocityTheory.ChartRestriction.G.I2
