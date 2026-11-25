-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_isSheet_planePt_91ba55760afb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:05.078682+00:00
-- url     : https://prove2.me/submissions/6b205057-3d1f-478d-b924-43ef81248f10

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjStdMassAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_proj_segre_planePt_3103a6de4ca8

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
theorem _root_.solution (hOf : ProjPtsOfPlane.Statement) {D : ℕ} (σ : K →+* ℂ) (y : Fin D → ℂ) :
    IsSheet (projSpaceIdeal K (D + 1)) projProj y
      (segre (ι := projBlocks K (D + 1)) (projPlanePt σ (Fin.cons 1 y)))
      (fun y' => projPlanePt σ (Fin.cons 1 y')) := by
  have hc : Differentiable ℂ (fun y' : Fin D → ℂ => (Fin.cons 1 y' : Fin (D + 1) → ℂ)) := by
    rw [differentiable_pi]
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · simpa using differentiable_apply (𝕜 := ℂ) k
  refine ⟨rfl, Filter.Eventually.of_forall fun y' => ⟨?_, ?_, proj_segre_planePt σ _⟩⟩
  · refine (differentiable_pi.mpr fun p => ?_) y'
    simp only [projPlanePt]
    exact (differentiable_pi.mp hc p.2.2).const_mul _
  · exact hOf K (D + 1) σ _ fun h0 => by simpa using congrFun h0 0
end GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
