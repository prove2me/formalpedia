-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_val_pullU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:47:03.960836+00:00
-- url     : https://prove2.me/submissions/c9d3e606-e4fb-4530-8b86-583b087c97aa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {Z Z' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (p : Sp ℂ ⟶ Z) (f : Z ⟶ Z') (U : Z'.Opens) (u : Γ(Z', U)ˣ) :
    valAt' p (f ⁻¹ᵁ U) (pullU f U u : Γ(Z, f ⁻¹ᵁ U)) = valAt' (p ≫ f) U (u : Γ(Z', U)) := by
  by_cases hc : ⊤ ≤ p ⁻¹ᵁ (f ⁻¹ᵁ U)
  · have hc' : ⊤ ≤ (p ≫ f) ⁻¹ᵁ U := fun x hx => hc hx
    rw [valAt', valAt', dif_pos hc, dif_pos hc']
    delta valAt pullU
    congr 1
  · have hc' : ¬ ⊤ ≤ (p ≫ f) ⁻¹ᵁ U := fun h' => hc (fun x hx => h' hx)
    rw [valAt', valAt', dif_neg hc, dif_neg hc']
end ReciprocityTheory.ChartRestriction.G.PullbackSections
