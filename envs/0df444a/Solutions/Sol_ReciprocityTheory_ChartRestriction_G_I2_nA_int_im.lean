-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_int_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:16:58.552586+00:00
-- url     : https://prove2.me/submissions/9a364586-0b61-44b3-809c-785c2b70a566

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_Hf_smul_right

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
theorem _root_.solution {q n : ℕ} {γ b : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L)
    (hb : ∀ k, (q : ℂ) • b k ∈ X.L) : ∃ m : ℤ, (q : ℝ) * (HC γ b).im = m := by
  choose m hm using fun k => X.integral (γ k) ((q : ℂ) • b k) (hγ k) (hb k)
  refine ⟨∑ k, m k, ?_⟩
  rw [HC, Complex.im_sum, Finset.mul_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hm k, nA_Hf_smul_right]
  simp [Complex.mul_im]
end ReciprocityTheory.ChartRestriction.G.I2
