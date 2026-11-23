-- Prove2me | solution 1 for PositivityTheory.RgJS.EulerProductLogLemmas.x_le_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:05.25941+00:00
-- url     : https://prove2.me/submissions/f4f6a70e-4ad3-4c10-b092-a903e3f886b4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_EulerLogarithms_EulerProductLogBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.RgJS
open PositivityTheory.RgJS.EulerProductLogLemmas
variable {W : Type} {A B : Type} [Fintype A] [Fintype B]
namespace PositivityTheory.RgJS.EulerProductLogLemmas
theorem _root_.solution {q : W → ℕ} {s : ℂ} (hq : ∀ w, 2 ≤ q w) (hs : 2 < s.re) (w : W) :
    (q w : ℝ) ^ (1 - s.re) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ q w := by exact_mod_cast hq w
  have h1 : (1 : ℝ) ≤ q w := by linarith
  calc (q w : ℝ) ^ (1 - s.re) ≤ (q w : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = (q w : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h2
end PositivityTheory.RgJS.EulerProductLogLemmas
