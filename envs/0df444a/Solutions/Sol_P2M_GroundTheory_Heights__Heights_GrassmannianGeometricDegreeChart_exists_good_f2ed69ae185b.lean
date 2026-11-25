-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_exists_good_f2ed69ae185b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:30:28.265851+00:00
-- url     : https://prove2.me/submissions/7593e59f-8479-452b-9bc1-5b332d453961

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassGeomDegChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassGeomDegChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_apply_eq_segre_ad27c26f28d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_card_seg_fc6c01e0c149

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
theorem _root_.solution (n : ℕ) :
    ∃ Ψ : (((k : Fin 1) → plBlocks 1 1 n k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ), IsGoodProj (grassIdeal 1 1 n) Ψ := by
  let Ψ0 := LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFinOfCardEq (card_seg (n := n))).symm
  refine ⟨Ψ0.toLinearMap, fun z hz h0 => ?_⟩
  obtain ⟨i, hi⟩ := hz.1 0
  have hs : segre (ι := plBlocks 1 1 n) z = 0 := Ψ0.map_eq_zero_iff.mp h0
  exact hi (by rw [apply_eq_segre z ⟨0, i⟩, hs]; rfl)
end GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
