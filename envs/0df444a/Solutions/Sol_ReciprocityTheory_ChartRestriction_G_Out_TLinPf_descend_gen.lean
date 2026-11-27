-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.descend_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:27:22.384842+00:00
-- url     : https://prove2.me/submissions/fd5dd093-429c-4ce3-9c10-0d03d95b3ce0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_DescGen

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
theorem _root_.solution {X Y : Scheme.{0}} (Q : X ⟶ Y) [Flat Q] [Surjective Q] [IsAffineHom Q]
    (ρ : Γ(X, ⊤))
    (hρ : ∀ {Z : Scheme.{0}} (y1 y2 : Z ⟶ X), y1 ≫ Q = y2 ≫ Q → y1.appTop.hom ρ = y2.appTop.hom ρ) :
    ∃ v : Γ(Y, ⊤), Q.appTop.hom v = ρ := by

  have hE : EffectiveEpi Q := by
    exact inferInstance

  obtain ⟨e, he⟩ : ∃ e, ∀ i : Fin 1, AffineSpace.toSpecMvPolyIntEquiv (Fin 1) e i = ρ :=
    ⟨(AffineSpace.toSpecMvPolyIntEquiv (Fin 1)).symm fun _ => ρ, fun i => by simp⟩
  have hcomp : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (i : Fin 1),
      AffineSpace.toSpecMvPolyIntEquiv (Fin 1) (g ≫ e) i = g.appTop.hom ρ := by
    intro Z g i
    rw [AffineSpace.toSpecMvPolyIntEquiv_comp, he]
  have hdesc : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ X), g₁ ≫ Q = g₂ ≫ Q → g₁ ≫ e = g₂ ≫ e := by
    intro Z g₁ g₂ h
    apply (AffineSpace.toSpecMvPolyIntEquiv (Fin 1)).injective
    funext i
    rw [hcomp, hcomp]
    exact hρ g₁ g₂ h
  refine ⟨AffineSpace.toSpecMvPolyIntEquiv (Fin 1) (EffectiveEpi.desc Q e hdesc) 0, ?_⟩
  have hf : AffineSpace.toSpecMvPolyIntEquiv (Fin 1) (Q ≫ EffectiveEpi.desc Q e hdesc) 0 = ρ := by
    rw [EffectiveEpi.fac, he]
  rw [AffineSpace.toSpecMvPolyIntEquiv_comp] at hf
  exact hf
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
