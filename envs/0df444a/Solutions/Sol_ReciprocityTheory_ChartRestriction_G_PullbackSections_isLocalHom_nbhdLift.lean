-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.isLocalHom_nbhdLift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:14.697065+00:00
-- url     : https://prove2.me/submissions/ecbaaa66-491a-4fc6-9719-91842425ee23

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_germ_nbhdLift

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
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution [IsLocalRing A] (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU)
    (hloc : ∀ (U : Y.Opens) (hU : y₀ ∈ U) (f : Γ(Y, U)), IsUnit (ψ U hU f) → y₀ ∈ Y.basicOpen f) :
    IsLocalHom (nbhdLift y₀ A ψ hψ).hom := by
  constructor
  intro a ha
  obtain ⟨U, hU, f, rfl⟩ := Y.presheaf.germ_exist a
  have e : (nbhdLift y₀ A ψ hψ).hom (Y.presheaf.germ U y₀ hU f) = ψ U hU f := by
    first
    | simpa using congrArg (fun g => g.hom f) (germ_nbhdLift ψ hψ U hU)
    | rw [← CommRingCat.comp_apply, germ_nbhdLift]
  rw [e] at ha
  first
  | exact (Y.mem_basicOpen f ⟨y₀, hU⟩).mp (hloc U hU f ha)
  | exact (Y.mem_basicOpen f y₀ hU).mp (hloc U hU f ha)
end ReciprocityTheory.ChartRestriction.G.PullbackSections
