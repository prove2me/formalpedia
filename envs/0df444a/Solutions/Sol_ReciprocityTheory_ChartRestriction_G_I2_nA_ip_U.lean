-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_ip_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:35:34.285941+00:00
-- url     : https://prove2.me/submissions/cb82754f-edab-4a4a-bb9f-e61d717c5f40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_sub_sub_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_exp_mul_conj
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
theorem _root_.solution (q : ℕ) {n : ℕ} (a : Fin n → Vsp X.dim) (F G : (Fin n → Vsp X.dim) → ℂ)
    (v : Fin n → Vsp X.dim) :
    X.U q a F v * (starRingEnd ℂ) (X.U q a G v) * ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ) =
      F (v - a) * (starRingEnd ℂ) (G (v - a)) *
        ((Real.exp (-(q * Real.pi) * (HC (v - a) (v - a)).re) : ℝ) : ℂ) := by
  unfold PT.U
  set z : ℂ := (q : ℂ) * Real.pi * HC v a - q * Real.pi * HC a a / 2 with hz
  have hre : 2 * z.re + (-(q * Real.pi) * (HC v v).re) = -(q * Real.pi) * (HC (v - a) (v - a)).re := by
    rw [hz, nA_re_U, nA_HC_sub_sub_re]; ring
  calc cexp z * F (v - a) * (starRingEnd ℂ) (cexp z * G (v - a)) *
        ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ)
      = (cexp z * (starRingEnd ℂ) (cexp z)) * (F (v - a) * (starRingEnd ℂ) (G (v - a))) *
          ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ) := by rw [map_mul]; ring
    _ = _ := by
      rw [nA_exp_mul_conj, ← hre, Real.exp_add, Complex.ofReal_mul]; ring
end ReciprocityTheory.ChartRestriction.G.I2
