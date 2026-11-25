-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion.app_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:17:05.464503+00:00
-- url     : https://prove2.me/submissions/85b635f0-5a55-4941-afbe-d121a940697d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_SurjOfCover

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
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion
variable {G B : Scheme.{0}} (q : G ⟶ B) {X : Type} [AddCommMonoid X] {W : B.Opens}
  (φ : ∀ V : B.Opens, V ≤ W → (Multiplicative X →* Γ(G, q ⁻¹ᵁ V)))
omit [AddCommMonoid X]
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion
theorem _root_.solution {V₁ V₂ : B.Opens} (h : V₁ ≤ V₂) (c : Γ(B, V₂)) :
    (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom ((q.app V₂).hom c) =
      (q.app V₁).hom ((B.presheaf.map (homOfLE h).op).hom c) := by
  have h2 := congrArg (fun f => f.hom c) (q.naturality (homOfLE h).op)
  first
  | exact h2.symm
  | simpa using h2.symm
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion
