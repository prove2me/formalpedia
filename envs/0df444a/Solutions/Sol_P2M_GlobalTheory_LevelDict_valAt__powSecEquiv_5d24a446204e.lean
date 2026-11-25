-- Prove2me | solution 1 for P2M_GlobalTheory_LevelDict_valAt__powSecEquiv_5d24a446204e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:50:15.531043+00:00
-- url     : https://prove2.me/submissions/3dc81d31-a9b5-4e5a-83f1-581f1432a57a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_UnimodularAndTangentOfIsAH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesTangentVectors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LineBundlePowSectionsEqThetaLevel
import Theorems.Thm_P2M_GlobalTheory_valAt__map_238ef0722272


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
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.LevelDict
variable {X : Scheme.{0}} (L : LB X) (n : ℕ)
namespace GlobalTheory.LevelDict
theorem _root_.solution (s : (lbPow L n).Sec) (x : Sp ℂ ⟶ X) (j : (lbPow L n).ι)
    (h : ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit)) :
    valAt' x (L.U (j PUnit.unit)) ((powSecEquiv L n s).f (j PUnit.unit)) = valAt' x ((lbPow L n).U j) (s.f j) :=
  valAt'_map x (homOfLE (le_powChart L n j)).op (s.f j) h
end GlobalTheory.LevelDict
