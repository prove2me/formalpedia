-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_planePt_injective_df97cc17290a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:07.047393+00:00
-- url     : https://prove2.me/submissions/b3401304-6edd-4aee-ac86-e9d1504b8c54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjStdMassAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_segre_const_65478bf974b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_embComp_planePt_6ec18513afa5

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
theorem _root_.solution {D : ℕ} (y : Fin D → ℂ) :
    Function.Injective fun σ : K →+* ℂ =>
      segre (ι := projBlocks K (D + 1)) (projPlanePt σ (Fin.cons 1 y)) := by
  classical
  intro σ τ h
  have h1 := congrArg (fun w : ((k : Unit) → projBlocks K (D + 1) k) → ℂ =>
    embComp σ (fun q => w fun _ => q)) h
  simp only [segre_const, embComp_planePt] at h1
  by_contra hne
  rw [if_pos trivial, if_neg fun e => hne e.symm] at h1
  simpa using congrFun h1 0
end GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
