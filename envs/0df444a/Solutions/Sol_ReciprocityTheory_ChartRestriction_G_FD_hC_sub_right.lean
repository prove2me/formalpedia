-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.hC_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:00.78651+00:00
-- url     : https://prove2.me/submissions/fc8455b6-e4ca-4ab8-8e47-f10040334d86

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
theorem _root_.solution (u v v' : Fin r → ℂ) :
    hermC τ G u (v - v') = hermC τ G u v - hermC τ G u v' := by
  simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
end ReciprocityTheory.ChartRestriction.G.FD
