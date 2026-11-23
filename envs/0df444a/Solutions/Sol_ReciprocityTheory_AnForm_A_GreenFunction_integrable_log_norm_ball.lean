-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.integrable_log_norm_ball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:39.766455+00:00
-- url     : https://prove2.me/submissions/e90dd0d9-b95e-4cca-90a4-576cff465618

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace intervalIntegral
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.GreenFunction
noncomputable section
namespace ReciprocityTheory.AnForm.A.GreenFunction
theorem _root_.solution {R : ℝ} (hR0 : 0 < R) :
    Integrable (fun z : ℂ => (Iic R).indicator (fun t => ‖Real.log t‖) ‖z‖) := by
  rw [integrable_fun_norm_addHaar volume (f := (Iic R).indicator (fun t => ‖Real.log t‖)),
    Complex.finrank_real_complex]
  have hcont : ContinuousOn (fun y : ℝ => ‖y * Real.log y‖) (Icc 0 R) :=
    (Real.continuous_mul_log.norm).continuousOn
  have h1 : IntegrableOn (fun y : ℝ => ‖y * Real.log y‖) (Ioc 0 R) :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun y : ℝ => y ^ (2 - 1) • (Iic R).indicator (fun t => ‖Real.log t‖) y)
      (Ioc 0 R) :=
    h1.congr_fun (fun y hy => by
      simp [indicator_of_mem (show y ∈ Iic R from hy.2), abs_of_pos hy.1]) measurableSet_Ioc
  have h3 : IntegrableOn (fun y : ℝ => y ^ (2 - 1) • (Iic R).indicator (fun t => ‖Real.log t‖) y)
      (Ioi R) :=
    (integrableOn_zero).congr_fun (fun y hy => by
      simp [indicator_of_notMem (show y ∉ Iic R by simp only [mem_Iic, not_le]; exact hy)]) measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi hR0.le]
  exact h2.union h3
end ReciprocityTheory.AnForm.A.GreenFunction
