-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_exp_antisymm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:10:36.542086+00:00
-- url     : https://prove2.me/submissions/986b28af-7c65-4024-b633-49f744f65ec3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E] (X : PT E)
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {n : ℕ} (q : ℕ) (γ b : Fin n → Vsp X.dim) (m : ℤ)
    (hm : (q : ℝ) * (HC γ b).im = m) :
    cexp ((q : ℂ) * Real.pi * (HC γ b - HC b γ)) = 1 := by
  rw [← nA_HC_conj γ b, Complex.sub_conj]
  have : (q : ℂ) * Real.pi * (((2 * (HC γ b).im : ℝ) : ℂ) * I) = (m : ℂ) * (2 * Real.pi * I) := by
    have hm' : ((q : ℝ) : ℂ) * (((HC γ b).im : ℝ) : ℂ) = (m : ℂ) := by
      rw [← Complex.ofReal_mul, hm]; simp
    push_cast at hm' ⊢
    linear_combination (2 * Real.pi * I) * hm'
  rw [this, Complex.exp_int_mul_two_pi_mul_I]
end ReciprocityTheory.ChartRestriction.G.I2
