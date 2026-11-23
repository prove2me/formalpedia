-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.nbhdPt_closedPoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:11.54823+00:00
-- url     : https://prove2.me/submissions/20953240-f7be-4085-a1a3-90e490345715

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isLocalHom_nbhdLift

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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
variable {Y : Scheme.{0}}
variable (y₀ : Y) (A : CommRingCat.{0})
variable {y₀ A}
set_option backward.isDefEq.respectTransparency false
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution [IsLocalRing A] (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU)
    (hloc : ∀ (U : Y.Opens) (hU : y₀ ∈ U) (f : Γ(Y, U)), IsUnit (ψ U hU f) → y₀ ∈ Y.basicOpen f) :
    nbhdPt ψ hψ (IsLocalRing.closedPoint A) = y₀ := by
  haveI := isLocalHom_nbhdLift ψ hψ hloc
  show (Y.fromSpecStalk y₀) ((Spec.map (nbhdLift y₀ A ψ hψ)) (IsLocalRing.closedPoint A)) = y₀
  have e : (Spec.map (nbhdLift y₀ A ψ hψ)) (IsLocalRing.closedPoint A) =
      IsLocalRing.closedPoint (Y.presheaf.stalk y₀) := by
    first
    | exact IsLocalRing.comap_closedPoint (nbhdLift y₀ A ψ hψ).hom
    | simp
  rw [e, Scheme.fromSpecStalk_closedPoint]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
