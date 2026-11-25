-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace.maj_le_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:02:11.356105+00:00
-- url     : https://prove2.me/submissions/1c163447-4c11-421f-9262-1f76ee3922a5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_norm_sq_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_maj_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (z : Frame X.Ψ r) (ξ : Fin r → E)
variable [hz : Fact (z ∈ X.dom)]
namespace ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace
theorem _root_.solution (u : VT (X := X) z ξ) (τ : X.Ψ) : X.maj z τ (u.val τ) ≤ ‖u‖ ^ 2 := by
  rw [norm_sq_eq]
  exact Finset.single_le_sum (fun σ _ => MajorantOperators.maj_nonneg hz.out σ _) (Finset.mem_univ τ)
end ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace
