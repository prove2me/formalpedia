-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.pa_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:16:45.625466+00:00
-- url     : https://prove2.me/submissions/5920d1c9-1a0a-4824-8842-ed6ee3a9cec4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_swap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_add_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex Metric
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (q : ℕ) (v g g' : EuclideanSpace ℂ ι) (kk : ℤ) (hkk : (Hf g' g).im = kk) :
    cexp (-(Real.pi * q * (Hf g g').im) * I) *
      cexp (q * Real.pi * Hf (v + g') (g + g') - q * Real.pi * Hf (g + g') (g + g') / 2) =
    cexp (q * Real.pi * Hf v g' + q * Real.pi * Hf g' g' / 2) *
      cexp (q * Real.pi * Hf v g - q * Real.pi * Hf g g / 2) := by
  set w := Hf g g' with hw
  have hconj : Hf g' g = w - 2 * (w.im : ℂ) * I := by
    rw [Hf_swap g g']
    apply Complex.ext <;> simp <;> ring
  have him : w.im = -kk := by
    have h1 : (Hf g' g).im = kk := hkk
    rw [hconj] at h1
    simp at h1
    linarith
  rw [← Complex.exp_add, ← Complex.exp_add]
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨q * kk, ?_⟩
  rw [Hf_add_left, Hf_add_right, Hf_add_right, Hf_add_left, Hf_add_right, Hf_add_right, hconj]
  push_cast
  rw [him]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.G.I2
