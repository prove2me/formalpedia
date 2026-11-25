-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_fibre_eq_077cda411379
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:02.57358+00:00
-- url     : https://prove2.me/submissions/4dc6e89f-af0e-4f07-9f85-d4913d13f72c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjStdMassAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_segre_const_65478bf974b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_embComp_planePt_6ec18513afa5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_proj_segre_planePt_3103a6de4ca8
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
theorem _root_.solution (hOn : ProjPtsOnPlane.Statement) (hOf : ProjPtsOfPlane.Statement) {D : ℕ}
    (y : Fin D → ℂ) :
    fibre (projSpaceIdeal K (D + 1)) projProj y =
      Set.range fun σ : K →+* ℂ => segre (ι := projBlocks K (D + 1)) (projPlanePt σ (Fin.cons 1 y)) := by
  classical
  ext w
  constructor
  · rintro ⟨z, hz, rfl, hΨ⟩
    obtain ⟨σ, hσ⟩ := hOn K (D + 1) z hz
    refine ⟨σ, congrArg segre ?_⟩
    have hW : ∀ τ : K →+* ℂ, embComp τ (fun q => z ⟨(), q⟩) =
        embComp τ (fun q => projPlanePt σ (Fin.cons 1 y) ⟨(), q⟩) := by
      intro τ
      rw [embComp_planePt]
      by_cases hτ : σ = τ
      · subst hτ
        rw [if_pos rfl, ← hΨ, projProj_apply]
        simp only [segre_const]
        exact (Finset.sum_eq_single σ (fun τ' _ h' => hσ τ' h') (by simp)).symm
      · rw [if_neg hτ]
        exact hσ τ (Ne.symm hτ)
    funext ⟨u, m, j⟩
    cases u
    refine ((sum_emb_embComp (fun q => projPlanePt σ (Fin.cons 1 y) ⟨(), q⟩) m j).symm.trans ?_).trans
      (sum_emb_embComp (fun q => z ⟨(), q⟩) m j)
    exact Finset.sum_congr rfl fun τ _ => by rw [hW τ]
  · rintro ⟨σ, rfl⟩
    have hv : (Fin.cons 1 y : Fin (D + 1) → ℂ) ≠ 0 := fun h0 => by simpa using congrFun h0 0
    exact ⟨_, hOf K (D + 1) σ _ hv, rfl, proj_segre_planePt σ _⟩
end GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
