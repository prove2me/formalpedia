-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.fn_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:31:33.9148+00:00
-- url     : https://prove2.me/submissions/3d1b1d62-7318-4f20-844a-a48855344ca0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DiagonalCurvatureCoefficient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LogpdAnalytic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology
variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution (v : Fin 1 → ℂ) : fn hm D Y v = ‖pd hm Y v‖ ^ 2 * fY hm D Y v := by
  have key : ∀ (p G : ℂ), (star p * (G * p)).re = ‖p‖ ^ 2 * G.re := by
    intro p G
    have h1 : star p * (G * p) = ((Complex.normSq p : ℝ) : ℂ) * G := by
      rw [Complex.star_def, ← Complex.mul_conj]
      ring
    rw [h1, Complex.re_ofReal_mul]
    first
    | rw [Complex.normSq_eq_norm_sq]
    | rw [← Complex.sq_norm]
    | simp [Complex.normSq_eq_norm_sq]
  simp only [fn, fY, Gnz, pd, Matrix.det_mul, Matrix.det_conjTranspose]
  exact key _ _
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
