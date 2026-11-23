-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.vanish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:43.553799+00:00
-- url     : https://prove2.me/submissions/e7ff0a7c-27e5-4577-b12d-75f768e16b70

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
theorem _root_.solution {u : ℂ → ℝ} {a : ℂ} {R : ℝ} (hR : ∀ z, R ≤ ‖z - a‖ → u z = 0) {z : ℂ}
    (hz : R < ‖z - a‖) : fderiv ℝ u z = 0 ∧ fderiv ℝ (fderiv ℝ u) z = 0 := by
  have hU : IsOpen {y : ℂ | R < ‖y - a‖} := isOpen_lt continuous_const (by fun_prop)
  have h1 : ∀ y ∈ {y : ℂ | R < ‖y - a‖}, fderiv ℝ u y = 0 := by
    intro y hy
    have : u =ᶠ[𝓝 y] fun _ => 0 :=
      Filter.eventually_of_mem (hU.mem_nhds hy) (fun x hx => hR x (le_of_lt hx))
    rw [this.fderiv_eq]; simp
  refine ⟨h1 z hz, ?_⟩
  have : fderiv ℝ u =ᶠ[𝓝 z] fun _ => 0 := Filter.eventually_of_mem (hU.mem_nhds hz) h1
  rw [this.fderiv_eq]; simp
end ReciprocityTheory.AnForm.A.GreenFunction
