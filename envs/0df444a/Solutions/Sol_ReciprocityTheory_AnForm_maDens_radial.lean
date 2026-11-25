-- Prove2me | solution 1 for ReciprocityTheory.AnForm.maDens_radial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:43.41124+00:00
-- url     : https://prove2.me/submissions/9249f87e-12bb-458f-aa25-38317dcc67df

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
import Theorems.Thm_ReciprocityTheory_AnForm_maDens_one
import Theorems.Thm_ReciprocityTheory_AnForm_fderiv_fderiv_radial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open MeasureTheory Filter Topology Set
noncomputable section
namespace ReciprocityTheory.AnForm
theorem _root_.solution (φ : Fin 1 → (Fin 1 → ℂ) → ℝ) (h h' h'' : ℝ → ℝ) (z : Fin 1 → ℂ)
    (hφ : φ 0 =ᶠ[𝓝 z] fun y => h (‖y 0‖ ^ 2))
    (hd : ∀ᶠ t in 𝓝 (‖z 0‖ ^ 2), HasDerivAt h (h' t) t)
    (hd2 : HasDerivAt h' (h'' (‖z 0‖ ^ 2)) (‖z 0‖ ^ 2)) :
    maDens φ z = 2 / Real.pi * (h'' (‖z 0‖ ^ 2) * ‖z 0‖ ^ 2 + h' (‖z 0‖ ^ 2)) := by
  rw [maDens_one]
  unfold levi
  rw [hφ.fderiv.fderiv_eq, fderiv_fderiv_radial h h' h'' z hd hd2,
    fderiv_fderiv_radial h h' h'' z hd hd2]
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Complex.inner,
    norm_one, Complex.norm_I]
  rw [← Complex.normSq_eq_norm_sq (z 0), Complex.normSq_apply]
  simp
  ring
end ReciprocityTheory.AnForm
