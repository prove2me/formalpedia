-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_isSmoothHerm_fs_e2b758fa739a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:56:52.929243+00:00
-- url     : https://prove2.me/submissions/0f9f22ce-c1c1-4839-ba58-8ed4432591c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FirstPointNeSecondPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_imaginaryPart_apply_dff8249560c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_norm_sq_eq_73ea6bfcdf63
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_nsq_pos_10fd427978dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_reP_apply_7da478929125


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
theorem _root_.solution {κ : Type} [Fintype κ] : IsSmoothHerm (HermLine.ofCone (fsMetric (Ix κ))) := by
  have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FSLevi.nsq (J := Ix κ)) := by
    unfold FSLevi.nsq
    exact ContDiff.sum fun p _ ↦ ((FSLevi.reP p).contDiff.pow 2).add ((FSLevi.imaginary p).contDiff.pow 2)
  have he : (HermLine.ofCone (fsMetric (Ix κ))).h = fun z ↦ Real.sqrt (FSLevi.nsq z) := by
    funext z
    simp [HermLine.ofCone, fsMetric, EuclideanSpace.norm_eq, FSLevi.nsq, FSLevi.reP_apply,
      FSLevi.imaginaryPart_apply, FSLevi.norm_sq_eq]
  unfold IsSmoothHerm
  rw [he]
  refine hN.contDiffOn.sqrt fun z hz ↦ (FSLevi.nsq_pos ?_).ne'
  obtain ⟨i, hi⟩ := hz ()
  exact fun h0 ↦ hi (congrFun h0 _)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
