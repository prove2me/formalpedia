-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_LocalPerfect_injective_compr__4c0b8fced67e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:10:18.6528+00:00
-- url     : https://prove2.me/submissions/a29bbfc2-b435-4a11-a460-71f51aa28e03

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalizationExact
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalPerfect_dualMap_bijective
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalPerfect_coefMap_bijective
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalPerfect_mapH2_cup_product_naturality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalPerfect
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]
  {D : Type*} [Group D] [TopologicalSpace D]
  (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (φ : D →* Γ) (χ' : D →* Rˣ)
namespace GlobalTheory.CompanionTheory.LocalPerfect
theorem _root_.solution (h : χ.comp φ = χ') (hc : ContAction (ρ.comp φ))
    (hc' : ContAction ((ρ.comp φ).comp (MonoidHom.id D)))
    (hq : ∀ (g : D) (m : R), ((charRep χ).comp φ) g m = charRep χ' g m)
    {P : H2 (charRep χ') →ₗ[R] R} (hP : Function.Injective P)
    (hL : Function.Injective (cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc'))
    (hF : Function.Injective (cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc').flip) :
    Function.Injective ((cupH1H1TwistedDual χ ρ φ hc).compr₂
        (P.comp (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq))) ∧
      Function.Injective ((cupH1H1TwistedDual χ ρ φ hc).compr₂
        (P.comp (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq))).flip := by
  have key : ∀ y x y' x', P (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq
        (cupH1H1TwistedDual χ ρ φ hc y x)) =
      P (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq
        (cupH1H1TwistedDual χ ρ φ hc y' x')) →
      cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc' (dualMap χ ρ φ χ' h y) (coefMap ρ φ x) =
      cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc' (dualMap χ ρ φ χ' h y') (coefMap ρ φ x') := by
    intro y x y' x' e
    have := hP e
    rwa [mapH2_cup_product_naturality χ ρ φ χ' h hc hc' hq, mapH2_cup_product_naturality χ ρ φ χ' h hc hc' hq] at this
  refine ⟨fun y y' e => (dualMap_bijective χ ρ φ χ' h).1 (hL (LinearMap.ext fun x => ?_)),
    fun x x' e => (coefMap_bijective ρ φ).1 (hF (LinearMap.ext fun y => ?_))⟩
  · obtain ⟨x, rfl⟩ := (coefMap_bijective ρ φ).2 x
    exact key y x y' x (LinearMap.congr_fun e x)
  · obtain ⟨y, rfl⟩ := (dualMap_bijective χ ρ φ χ' h).2 y
    exact key y x y x' (LinearMap.congr_fun e y)
end GlobalTheory.CompanionTheory.LocalPerfect
