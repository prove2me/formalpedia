-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_embComp_planePt_6ec18513afa5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:01.06181+00:00
-- url     : https://prove2.me/submissions/fd5468c9-c225-41ff-beaf-31f183b9ffed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjStdMassAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_repr_sum_de623f64b805

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
open Classical
namespace GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
theorem _root_.solution {i : ℕ} (τ σ : K →+* ℂ) (v : Fin i → ℂ) :
    embComp τ (fun q => projPlanePt σ v ⟨(), q⟩) = if σ = τ then v else 0 := by
  funext j
  have h : ∑ m, (canonicalEmbedding.latticeBasis K).repr (Pi.single τ 1) m *
      (σ (integralBasis K m) * v j) = (if σ = τ then 1 else 0) * v j := by
    rw [← repr_sum τ σ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  simp only [embComp, projPlanePt]
  rw [h]
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
