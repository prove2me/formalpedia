-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualGeomDegCharts_proof_d873f9307c28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:24.622856+00:00
-- url     : https://prove2.me/submissions/e960bc78-1b22-488b-bade-c9490968d2f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualGeomDegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOfPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_dualProj_good_edb0e81a6984
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_atProj_dc3d820b7c5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPtsOfPlane_proof_4394ca2b9395
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPtsOnPlane_proof_e41a18cf842f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualStdMassAt_proof_fd101889fa59


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
open ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter Topology Matrix NumberField
open scoped ComplexOrder
noncomputable section
open DualGeometricDegreeCharts
namespace GroundTheory.Heights₂.Heights
namespace DualGeomDegCharts
theorem _root_.solution (hInt : ChartDensityIntegrable.Statement) : DualGeomDegCharts.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨D, rfl⟩ : ∃ D, i = D + 1 := ⟨i - 1, by omega⟩
  have hex : ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (dualIdeal b) Ψ := ⟨_, dualProj_good DualPtsOnPlane.proof b hb⟩
  obtain ⟨A, hA, hE⟩ := atProj DualPtsOnPlane.proof DualPtsOfPlane.proof hInt b hb hex.choose hex.choose_spec
  refine ⟨A, hA, ?_⟩
  show ptsIntegral (e := D) (dualIdeal b) (fun _ z => Real.log ((dualLine F b hb).h z)) (fun _ => 1) = _
  unfold ptsIntegral
  rw [dif_pos hex]
  exact hE
end DualGeomDegCharts
end GroundTheory.Heights₂.Heights
