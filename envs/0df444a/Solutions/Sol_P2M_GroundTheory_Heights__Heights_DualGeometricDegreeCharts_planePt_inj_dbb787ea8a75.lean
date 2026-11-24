-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_planePt_inj_dbb787ea8a75
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:08.805655+00:00
-- url     : https://prove2.me/submissions/76ff77c2-ef16-443d-b6d2-9e97ca53b5b8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualGeomDegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOfPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_recover_planePt_b75c0350c21e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_segre_const_b90202405c1e


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
omit [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.DualGeometricDegreeCharts
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) {σ τ : K →+* ℂ}
    {v u : Fin (D + 1) → ℂ} (hv : v ≠ 0)
    (h : segre (ι := dualBlocks T) (dualPlanePt b σ v) = segre (ι := dualBlocks T) (dualPlanePt b τ u)) :
    σ = τ := by
  have h1 := congrArg (fun w : ((k : Unit) → dualBlocks T k) → ℂ =>
    dualRecover b hb (fun t => w fun _ => t)) h
  simp only [segre_const, recover_planePt] at h1
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  have h2 := congrFun h1 (σ, j)
  by_contra hne
  exact hj (by simpa [hne] using h2)
end GroundTheory.Heights₂.Heights.DualGeometricDegreeCharts
