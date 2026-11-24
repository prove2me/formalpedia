-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_segre_const_b90202405c1e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:51:09.745531+00:00
-- url     : https://prove2.me/submissions/828373e0-f744-40e1-8d17-f084cba7e766

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]
omit [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
theorem _root_.solution (z : (Σ _ : Unit, T) → ℂ) (t : T) :
    segre (ι := dualBlocks T) z (fun _ => t) = z ⟨(), t⟩ := by
  simp [segre]
end GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
