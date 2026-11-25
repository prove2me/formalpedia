-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.Jp_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:08.375227+00:00
-- url     : https://prove2.me/submissions/6a37225e-2c5e-4390-8519-d16ae977e624

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_sub


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
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.Jp x τ (u - v) = X.Jp x τ u - X.Jp x τ v := by
  unfold Jp
  rw [X.ppos_sub, smul_sub]
  abel
end ReciprocityTheory.ChartRestriction.G.FD.Data
