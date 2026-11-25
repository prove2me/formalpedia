-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.isPshInhabit_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:31.877516+00:00
-- url     : https://prove2.me/submissions/b07a2eaf-8fb5-4b09-9704-3c965c8748ed

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_plurisubharmonicIffLeviNonneg_holds
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshInh_ci_of_cont
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshInh_le_avg_norm
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshInh_le_avg_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Set Filter Topology Real PshInh
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : IsPshInhabitStatement := by
  intro D
  have hsq : IsPsh (Set.univ : Set (Fin D → ℂ)) (fun z => ∑ j, ‖z j‖ ^ 2) := by
    refine ⟨(by fun_prop : Continuous (fun z : Fin D → ℂ => ∑ j, ‖z j‖ ^ 2)).continuousOn.upperSemicontinuousOn,
      fun z w _ => ⟨ci_of_cont (by fun_prop), ?_⟩⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Real.circleAverage_fun_sum (fun j _ => ci_of_cont (by fun_prop))]
    exact Finset.sum_le_sum fun j _ => le_avg_sq (z j) (w j)
  have hnorm : IsPsh (Set.univ : Set (Fin D → ℂ)) (fun z => ‖z‖) := by
    refine ⟨continuous_norm.continuousOn.upperSemicontinuousOn,
      fun z w _ => ⟨ci_of_cont (by fun_prop), ?_⟩⟩
    show ‖z‖ ≤ Real.circleAverage (fun ζ : ℂ => ‖z + ζ • w‖) 0 1
    rcases isEmpty_or_nonempty (Fin D) with hD | hD
    · rw [Subsingleton.elim z 0, norm_zero]
      exact Real.circleAverage_nonneg_of_nonneg fun _ _ => norm_nonneg _
    · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
        (fun b => ‖z b‖₊)
      have hzj : ‖z‖ = ‖z j‖ := by rw [Pi.norm_def, hj]; rfl
      rw [hzj]
      refine (le_avg_norm (z j) (w j)).trans (Real.circleAverage_mono (ci_of_cont (by fun_prop))
        (ci_of_cont (by fun_prop)) fun ζ _ => ?_)
      simpa using norm_le_pi_norm (z + ζ • w) j
  have hC : ContDiffOn ℝ 2 (fun z : Fin D → ℂ => ∑ j, ‖z j‖ ^ 2) Set.univ :=
    (ContDiff.sum fun j _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ j)).contDiffOn
  refine ⟨hsq, hnorm, (PshLap.plurisubharmonicIffLeviNonneg_holds D _ _ isOpen_univ hC).1 hsq, ?_⟩
  rintro ⟨-, h2⟩
  have h := (h2 0 (Pi.single 0 1) (fun _ _ => Set.mem_univ _)).2
  rw [Real.circleAverage_const_on_circle (a := (-1:ℝ)) (fun x hx => by
    simp only [mem_sphere_iff_norm, sub_zero, abs_one] at hx
    simp [hx])] at h
  norm_num at h
end ReciprocityTheory.AnForm.A
