-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_segre_const_65478bf974b7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:08.059791+00:00
-- url     : https://prove2.me/submissions/209095f0-1779-4da6-b859-6b4b928d82df

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjStdMassAt

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
theorem _root_.solution {i : ℕ} (z : (Σ _ : Unit, ProjIdx K i) → ℂ) (q : ProjIdx K i) :
    segre (ι := projBlocks K i) z (fun _ => q) = z ⟨(), q⟩ := by
  simp [segre]
end GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
