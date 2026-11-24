-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_hermChartPot_eq_289dc0484b46
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:07.158805+00:00
-- url     : https://prove2.me/submissions/5499f67c-9eaa-4069-9665-839941c1d7b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualGeomDegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOfPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegCharts

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
theorem _root_.solution (A h : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) (y : Fin D → ℂ) :
    hermChartPot (Aᴴ * h * A) y =
      Real.log (Real.sqrt (star (A *ᵥ Fin.cons 1 y) ⬝ᵥ (h *ᵥ (A *ᵥ Fin.cons 1 y))).re) := by
  unfold hermChartPot
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
end GroundTheory.Heights₂.Heights.DualGeometricDegreeCharts
