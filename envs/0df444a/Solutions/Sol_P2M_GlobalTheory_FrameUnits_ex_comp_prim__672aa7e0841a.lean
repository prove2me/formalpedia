-- Prove2me | solution 1 for P2M_GlobalTheory_FrameUnits_ex_comp_prim__672aa7e0841a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:50:37.546083+00:00
-- url     : https://prove2.me/submissions/67c6a70a-1d0a-4bb6-95eb-12a75889b6e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
import Theorems.Thm_GlobalTheory_FrameUnits_primLin_apply
import Theorems.Thm_GlobalTheory_CubeValues_ex_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open GlobalTheory.JetSer (IsNormRos primφ primε)
open GlobalTheory.CubeValues GlobalTheory.AppellHumbertTrivial
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.FrameUnits
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.FrameUnits
theorem _root_.solution {w : A ⟶ A} {W : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (hW : ∀ z, u.ex (W z) = u.ex z ≫ w)
    (k : Fin 5) (z : Fin g → ℂ) : (u.ex z).left ≫ primφ w k = (u.ex (primLin W k z)).left := by
  have key : ∀ (q : A ⟶ A) y, u.ex z ≫ q = u.ex y → (u.ex z).left ≫ q.left = (u.ex y).left :=
    fun q w e => congrArg (·.left) e
  rw [primLin_apply]
  fin_cases k
  · exact Category.comp_id _
  · refine key (𝟙 A * w) (z + W z) ?_
    simp [MonObj.comp_mul, u.ex_add, hW]
  · exact Category.comp_id _
  · exact key w (W z) (hW z).symm
  · refine key 1 0 ?_
    simp [ex_zero u]
end GlobalTheory.FrameUnits
