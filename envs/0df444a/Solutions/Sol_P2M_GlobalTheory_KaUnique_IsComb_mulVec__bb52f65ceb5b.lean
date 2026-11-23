-- Prove2me | solution 1 for P2M_GlobalTheory_KaUnique_IsComb_mulVec__bb52f65ceb5b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:53.046484+00:00
-- url     : https://prove2.me/submissions/383dfc70-d919-4b5a-a2b7-a76b00ee4c54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignSwap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TopLeTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KaUnique
variable {R : Type} [CommRing R] {X : Scheme.{0}} (π : X ⟶ Sp R) (L : LB X)
variable {π L}
namespace GlobalTheory.KaUnique
namespace IsComb
theorem _root_.solution {N N' : ℕ} {b : Fin N → ∀ i, Γ(X, L.U i)} {b' : Fin N' → ∀ i, Γ(X, L.U i)}
    {M : Matrix (Fin N) (Fin N') R} {f : ∀ i, Γ(X, L.U i)} {e : Fin N' → R}
    (hM : ∀ k, IsComb π L b (fun k' => M k' k) (b' k)) (he : IsComb π L b' e f) :
    IsComb π L b (M.mulVec e) f := by
  have := IsComb.mulVec (u := fun _ => 1) (M := M) (b := b) (b' := b') (by simpa only [_root_.one_mul] using hM) he
  simpa only [_root_.one_mul] using this
end IsComb
end GlobalTheory.KaUnique
