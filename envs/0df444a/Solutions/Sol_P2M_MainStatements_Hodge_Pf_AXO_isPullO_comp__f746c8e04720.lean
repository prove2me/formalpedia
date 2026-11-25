-- Prove2me | solution 1 for P2M_MainStatements_Hodge_Pf_AXO_isPullO_comp__f746c8e04720
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:15.030284+00:00
-- url     : https://prove2.me/submissions/99246502-1375-4fd2-8ca7-42de347900f6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_CompositeRestrictionPullInjective
import Theorems.Thm_MainStatements_Hodge_Pf_AXO_isPullO_comp
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp


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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open MainStatements MainStatements.Hodge MainStatements.Hodge.Pf MainStatements.Hodge.Pf.AXO
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}
namespace MainStatements.Hodge.Pf.AXO
theorem _root_.solution {ρ : R →+* R''} (hρ : τ.comp σ = ρ) (h : φ ≫ s = s' ≫ spMap σ)
    (h' : ψ ≫ s' = s'' ≫ spMap τ) (χ : X'' ⟶ X) (hχ : χ = ψ ≫ φ) (h'' : χ ≫ s = s'' ≫ spMap ρ) (a : HO1 s)
    (a' : HO1 s') (a'' : HO1 s'') (p : IsPullO h a a') (p' : IsPullO h' a' a'') : IsPullO h'' a a'' := by
  subst hχ; exact isPullO_comp hρ h h' h'' a a' a'' p p'
end MainStatements.Hodge.Pf.AXO
