-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.pointwiseNormSq_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:34:54.359186+00:00
-- url     : https://prove2.me/submissions/3e4fb39c-2134-4472-afc0-35fa497bdaa9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_sub_sub_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_re_U

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
theorem _root_.solution (q : ℕ) {n : ℕ} (a : Fin n → Vsp X.dim) (F : (Fin n → Vsp X.dim) → ℂ)
    (v : Fin n → Vsp X.dim) : X.ptN2 q (X.U q a F) v = X.ptN2 q F (v - a) := by
  unfold PT.ptN2 PT.U
  set z : ℂ := (q : ℂ) * Real.pi * HC v a - q * Real.pi * HC a a / 2 with hz
  have hre : 2 * z.re + (-(q * Real.pi) * (HC v v).re) = -(q * Real.pi) * (HC (v - a) (v - a)).re := by
    rw [hz, nA_re_U, nA_HC_sub_sub_re]; ring
  rw [norm_mul, Complex.norm_exp, mul_pow, ← hre, Real.exp_add, sq (Real.exp z.re), ← Real.exp_add]
  ring_nf
end ReciprocityTheory.ChartRestriction.G.I2
