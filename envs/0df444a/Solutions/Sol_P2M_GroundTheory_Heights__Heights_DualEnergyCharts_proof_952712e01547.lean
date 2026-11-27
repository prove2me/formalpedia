-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualEnergyCharts_proof_952712e01547
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:54:40.729339+00:00
-- url     : https://prove2.me/submissions/8777bc14-fd3d-4b07-9658-8b0743fda11a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualEnergyCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualEnergyCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualEnergyChartsAlt_atProj_3fe6f750663d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeomDegCharts_proof_d873f9307c28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_atProj_dc3d820b7c5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_dualProj_good_edb0e81a6984
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
open DualEnergyChartsAlt DualGeometricDegreeCharts
namespace GroundTheory.Heights₂.Heights
namespace DualEnergyCharts
theorem _root_.solution (hInt : ChartEnergyIntegrable.Statement) : DualEnergyCharts.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨D, rfl⟩ : ∃ D, i = D + 1 := ⟨i - 1, by omega⟩
  have hex : ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (dualIdeal b) Ψ := ⟨_, dualProj_good DualPtsOnPlane.proof b hb⟩
  obtain ⟨hA, hE⟩ := atProj DualPtsOnPlane.proof DualPtsOfPlane.proof hInt b hb hex.choose hex.choose_spec
  refine ⟨chartMat DualPtsOfPlane.proof b hb hex.choose_spec, hA, fun k => ?_⟩
  show ptsIntegral (e := D) (dualIdeal b)
      (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
      (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) = _
  unfold ptsIntegral
  rw [dif_pos hex]
  exact hE k
end DualEnergyCharts
end GroundTheory.Heights₂.Heights
