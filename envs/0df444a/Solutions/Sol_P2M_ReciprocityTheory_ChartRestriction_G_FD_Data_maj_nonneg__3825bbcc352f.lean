-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_nonneg__3825bbcc352f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:56.45026+00:00
-- url     : https://prove2.me/submissions/9bdad958-4afa-4ae7-b62d-01dc89d4c0fc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_zero__8e14f778d7b3

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
theorem _root_.solution (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ))
    (hpos : ∀ v, v ≠ 0 → 0 < X.maj x τ v) (v : Fin r → ℂ) : 0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · rw [hv, X.maj_zero' hself]
  · exact (hpos v hv).le
end ReciprocityTheory.ChartRestriction.G.FD.Data
