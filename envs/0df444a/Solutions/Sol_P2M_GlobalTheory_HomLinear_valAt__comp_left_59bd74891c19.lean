-- Prove2me | solution 1 for P2M_GlobalTheory_HomLinear_valAt__comp_left_59bd74891c19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:04:52.343775+00:00
-- url     : https://prove2.me/submissions/f728d8f1-c58d-4f3f-a858-adecdb45d352

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVarietStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom
import Theorems.Thm_P2M_GlobalTheory_valAt__comp_7a5ff8fa895a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HomLinear
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
omit [GrpObj A] [GrpObj A']
namespace GlobalTheory.HomLinear
theorem _root_.solution (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (f : A ⟶ A') (U : A'.left.Opens) (s : Γ(A'.left, U)) :
    valAt' (x ≫ f).left U s = valAt' x.left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s) :=
  (valAt'_comp x.left f.left U s).symm
end GlobalTheory.HomLinear
