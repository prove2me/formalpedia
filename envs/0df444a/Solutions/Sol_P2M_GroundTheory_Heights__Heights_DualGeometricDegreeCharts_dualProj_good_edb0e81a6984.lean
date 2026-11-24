-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_dualProj_good_edb0e81a6984
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:36.269049+00:00
-- url     : https://prove2.me/submissions/e8efcaf5-9e76-4ac2-a763-905bda080cd7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualGeomDegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOfPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_eq_planePt_3508fd5ed475
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_segre_const_b90202405c1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_dualProj_apply_5ec1a7484f01


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
open GroundTheory.Heights₂.Heights.DualGeometricDegreeCharts
open StandardDualMassAtPoint
variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]
  {D : ℕ} {F : HermLattice K (D + 1)}
namespace GroundTheory.Heights₂.Heights.DualGeometricDegreeCharts
theorem _root_.solution (hOn : DualPtsOnPlane.Statement) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    IsGoodProj (dualIdeal b) (dualProj b hb) := by
  intro z hz h0
  obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
  have hz' := eq_planePt b hb hσ
  have hp : dualProj b hb (segre z) = recLin b hb σ z := by
    funext j
    simp only [dualProj_apply, segre_const]
    exact Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ j) (by simp)
  rw [hp] at h0
  obtain ⟨t, ht⟩ := hz.1 ()
  apply ht
  rw [hz', h0]
  simp [dualPlanePt]
end GroundTheory.Heights₂.Heights.DualGeometricDegreeCharts
