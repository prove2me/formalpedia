-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.hC_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:47.418574+00:00
-- url     : https://prove2.me/submissions/d903f195-0974-4abf-b546-04e541c5624e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable section
variable {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution (v : Fin r → ℂ) : hermC τ G 0 v = 0 := by
  simp [hermC]
end ReciprocityTheory.ChartRestriction.G.FD
