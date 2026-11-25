-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__comp_88757af08841
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:34:37.10551+00:00
-- url     : https://prove2.me/submissions/e5546b13-07d8-49de-b700-8a5e46d648c0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {g : ℕ} {Y Y' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Y') (U : Y'.Opens) (f : Γ(Y', U)) :
    valAt' x (φ ⁻¹ᵁ U) (φ.app U f) = valAt' (x ≫ φ) U f := by
  unfold valAt'
  have e : x ⁻¹ᵁ φ ⁻¹ᵁ U = (x ≫ φ) ⁻¹ᵁ U := rfl
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · rw [dif_pos (e ▸ h), dif_pos h]
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · rw [dif_neg (e ▸ h), dif_neg h]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
