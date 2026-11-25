-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.lap_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:28.926463+00:00
-- url     : https://prove2.me/submissions/2d79fa33-4c1e-4de9-ad53-9567192ce391

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_laplacian_eq_fderiv_fderiv
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_vanish

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
theorem _root_.solution {u : ℂ → ℝ} {a : ℂ} {R : ℝ} (hR : ∀ z, R ≤ ‖z - a‖ → u z = 0) {z : ℂ}
    (hz : R < ‖z - a‖) : Δ u z = 0 := by
  rw [laplacian_eq_fderiv_fderiv, (vanish hR hz).2]; simp
end ReciprocityTheory.AnForm.A.GreenFunction
