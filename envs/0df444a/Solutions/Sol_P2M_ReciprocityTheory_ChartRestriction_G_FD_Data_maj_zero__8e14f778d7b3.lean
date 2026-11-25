-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_zero__8e14f778d7b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:50.986093+00:00
-- url     : https://prove2.me/submissions/3fc1c45b-3e11-4832-a0e6-bcecb283af83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_smul

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
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
variable {x : Frame X.Ψ r} {τ : X.Ψ}
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ)) : X.maj x τ 0 = 0 := by
  have h1 := X.maj_smul hself (0 : ℂ) 0
  simpa using h1
end ReciprocityTheory.ChartRestriction.G.FD.Data
