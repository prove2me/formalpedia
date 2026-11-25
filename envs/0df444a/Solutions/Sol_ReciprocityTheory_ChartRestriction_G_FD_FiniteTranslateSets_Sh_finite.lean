-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FiniteTranslateSets.Sh_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:37.911573+00:00
-- url     : https://prove2.me/submissions/45fefae9-fca6-4a6f-bf11-811a2039cf47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FiniteTranslateSets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.FiniteTranslateSets
open NumberField Module
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FiniteTranslateSets
theorem _root_.solution (R : ℝ) (hR : 0 ≤ R) : (Sh X R).Finite := by
  have hS := NumberField.Embeddings.finite_of_norm_le E ℂ R
  have hd : ((X.den : 𝓞 E) : E) ≠ 0 := by exact_mod_cast X.den_ne
  refine (hS.image fun x => x / (X.den : E)).subset ?_
  rintro β ⟨α, hα, hb⟩
  refine ⟨(α : E), ⟨α.isIntegral_coe, hb⟩, ?_⟩
  show (α : E) / (X.den : E) = β
  rw [hα]
  field_simp
end ReciprocityTheory.ChartRestriction.G.FD.FiniteTranslateSets
