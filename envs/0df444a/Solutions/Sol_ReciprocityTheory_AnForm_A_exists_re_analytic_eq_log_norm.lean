-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.exists_re_analytic_eq_log_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:51.745079+00:00
-- url     : https://prove2.me/submissions/9e1e5506-5347-4fd4-ae6b-5077fa069849

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Complex Filter Topology
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hg : AnalyticAt ℂ g z) (hz : g z ≠ 0) :
    ∃ G : (Fin D → ℂ) → ℂ, AnalyticAt ℂ G z ∧
      (fun w => Real.log ‖g w‖) =ᶠ[𝓝 z] fun w => (G w).re := by
  refine ⟨fun w => Complex.log (g w / g z) + Complex.log (g z), ?_, ?_⟩
  · refine AnalyticAt.add ?_ analyticAt_const
    refine (hg.div analyticAt_const hz).clog ?_
    show g z / g z ∈ Complex.slitPlane
    rw [div_self hz]
    exact Complex.one_mem_slitPlane
  · filter_upwards [hg.continuousAt.eventually_ne hz] with w hw
    simp only [Complex.add_re, Complex.log_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.2 hw) (norm_ne_zero_iff.2 hz)]
    ring
end ReciprocityTheory.AnForm.A
