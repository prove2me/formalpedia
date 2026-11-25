-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_U_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:27:55.025922+00:00
-- url     : https://prove2.me/submissions/231bae01-5726-4704-950d-84eef30cacb8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_sub_left

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
theorem _root_.solution (q : ℕ) {n : ℕ} (k b : Fin n → Vsp X.dim) (F : (Fin n → Vsp X.dim) → ℂ)
    (v : Fin n → Vsp X.dim) :
    X.U q k (X.U q b F) v = cexp ((q : ℂ) * Real.pi * (HC b k - HC k b)) * X.U q b (X.U q k F) v := by
  unfold PT.U
  rw [sub_right_comm v k b, nA_HC_sub_left, nA_HC_sub_left]
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring
end ReciprocityTheory.ChartRestriction.G.I2
