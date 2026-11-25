-- Prove2me | solution 1 for P2M_GlobalTheory_SpreadScheme_PairModel_baseChange_a__p__b9f293c1f024
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:14:59.9878+00:00
-- url     : https://prove2.me/submissions/a1b3d71e-0e4d-484d-bd40-090494aaaae9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SpreadScheme
open GlobalTheory.Spread GlobalTheory.GlueModels
attribute [instance] PairModel.lfp PairModel.qs PairModel.qc PairModel.opn PairModel.qca
variable {S S₁ S₀ U T : Scheme.{0}} {f : S ⟶ S₀} {p : U ⟶ S} {a : T ⟶ U}
namespace GlobalTheory.SpreadScheme
namespace PairModel
theorem _root_.solution (M : PairModel f p a) (σ : S ⟶ S₁) (g : S₁ ⟶ S₀) (e : σ ≫ g = f) :
    (M.baseChange σ g e).a₀ ≫ (M.baseChange σ g e).p₀ = pullback.snd (M.a₀ ≫ M.p₀) g :=
  pullback.lift_snd _ _ _
end PairModel
end GlobalTheory.SpreadScheme
