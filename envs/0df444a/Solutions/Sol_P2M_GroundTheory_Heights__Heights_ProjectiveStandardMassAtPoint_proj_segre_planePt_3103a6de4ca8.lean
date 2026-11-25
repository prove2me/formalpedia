-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_proj_segre_planePt_3103a6de4ca8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:50.377069+00:00
-- url     : https://prove2.me/submissions/bb3330ee-976b-4363-bde0-6cd95a4c68ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjStdMassAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_segre_const_65478bf974b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_embComp_planePt_6ec18513afa5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_projProj_apply_f07037b926be


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
theorem _root_.solution {i : ℕ} (σ : K →+* ℂ) (v : Fin i → ℂ) :
    projProj (segre (ι := projBlocks K i) (projPlanePt σ v)) = v := by
  classical
  rw [projProj_apply]
  simp only [segre_const, embComp_planePt]
  rw [Finset.sum_eq_single σ (fun τ _ hτ => if_neg (Ne.symm hτ)) (by simp)]
  exact if_pos rfl
end GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
