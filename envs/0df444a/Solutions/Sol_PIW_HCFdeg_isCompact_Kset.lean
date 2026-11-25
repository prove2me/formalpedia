-- Prove2me | solution 1 for PIW.HCFdeg.isCompact_Kset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:24:21.386103+00:00
-- url     : https://prove2.me/submissions/d7338477-4b30-49c4-8800-8433632eb16b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory PI.UpqRep Matrix
open scoped MatrixOrder NNReal ENNReal ComplexOrder Pointwise
variable {n : ℕ} (ε : Fin n → Bool)
namespace PIW.HCFdeg
theorem _root_.solution : IsCompact (Kset ε) := by
  unfold Kset
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hK.of_isClosed_subset ?_ ?_
  · refine IsClosed.inter (s₁ := {g : Matrix (Fin n) (Fin n) ℂ | g ∈ unitaryGroup (Fin n) ℂ})
      (s₂ := {g : Matrix (Fin n) (Fin n) ℂ | g * Jm ε = Jm ε * g}) ?_ ?_
    · have e : {g : Matrix (Fin n) (Fin n) ℂ | g ∈ unitaryGroup (Fin n) ℂ} = {g | g * star g = 1} :=
        Set.ext fun g => mem_unitaryGroup_iff
      rw [e]
      exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const
    · exact isClosed_eq (continuous_id.matrix_mul continuous_const) (continuous_const.matrix_mul continuous_id)
  · rintro (g : Matrix (Fin n) (Fin n) ℂ) ⟨hg, -⟩
    refine Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have hu : g * gᴴ = 1 := mem_unitaryGroup_iff.mp hg
    have h := congrFun (congrFun hu i) i
    rw [Matrix.mul_apply] at h
    simp only [Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
    have h2 : ∑ k, ‖g i k‖ ^ 2 = 1 := by
      have h4 : ∑ k, g i k * star (g i k) = ∑ k, ((‖g i k‖ ^ 2 : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [h4, ← Complex.ofReal_sum] at h
      exact_mod_cast h
    have h3 : ‖g i j‖ ^ 2 ≤ 1 := h2 ▸ Finset.single_le_sum (fun k _ => sq_nonneg ‖g i k‖) (Finset.mem_univ j)
    nlinarith [norm_nonneg (g i j)]
end PIW.HCFdeg
