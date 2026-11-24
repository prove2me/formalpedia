-- Prove2me | solution 1 for P2M_GlobalTheory_FrameValue_valAt__gen_b257caf834b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:15:40.725137+00:00
-- url     : https://prove2.me/submissions/aaf2fc3a-41ce-42aa-9d00-f293266142fc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Theorems.Thm_P2M_GlobalTheory_FrameValue_valAt__sec_9a5221679090

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FrameValue
open CubeValues SymmetricSemicharacter EigenNorm
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {Y Y' : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ A.left)} {ε' : K' → ℤ}
variable {u}
namespace GlobalTheory.FrameValue
theorem _root_.solution (hL : L.IsLB) {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ}
    (hz : IsLift u φ y z) {j : K → L.ι} (hj : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j) :
    valAt' y (L.wchart φ j) (t.s j).val = genVal u hL t y z * frameProd u ε z j :=
  valAt'_sec hL (genSec t ht) hz hj
end GlobalTheory.FrameValue
