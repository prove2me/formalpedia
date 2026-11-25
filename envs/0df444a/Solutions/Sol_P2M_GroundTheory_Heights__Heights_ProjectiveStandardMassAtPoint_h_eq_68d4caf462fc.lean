-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_h_eq_68d4caf462fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:53.002816+00:00
-- url     : https://prove2.me/submissions/fa7ae471-816a-4928-a862-c8525e8b17e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjStdMassAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_segre_const_65478bf974b7
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
theorem _root_.solution (hOn : ProjPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) {z : (Σ _ : Unit, ProjIdx K (D + 1)) → ℂ}
    (hz : z ∈ mcPts (projSpaceIdeal K (D + 1))) :
    (latticeLine F).h z = Real.sqrt (∑ j, ‖projProj (segre (ι := projBlocks K (D + 1)) z) j‖ ^ 2) := by
  obtain ⟨σ, hσ⟩ := hOn K (D + 1) z hz
  have hp : projProj (segre (ι := projBlocks K (D + 1)) z) = embComp σ (fun q => z ⟨(), q⟩) := by
    rw [projProj_apply]
    simp only [segre_const]
    exact Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ) (by simp)
  show Real.sqrt (latticeNormSq F fun q => z ⟨(), q⟩) = _
  congr 1
  rw [latticeNormSq, Finset.sum_eq_single σ]
  · rw [hF, one_mulVec, dotProduct, Complex.re_sum, hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  · intro τ _ hτ
    rw [hσ τ hτ]
    simp
  · simp
end GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
