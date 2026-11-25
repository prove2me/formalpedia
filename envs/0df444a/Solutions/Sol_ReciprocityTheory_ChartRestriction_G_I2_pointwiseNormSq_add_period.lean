-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.pointwiseNormSq_add_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:40:30.688886+00:00
-- url     : https://prove2.me/submissions/0f250813-f059-48c1-a828-7e2396fbd6e8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_add_add_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_re_S
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_epsprod_norm

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
theorem _root_.solution {q n : ℕ} {F : (Fin n → Vsp X.dim) → ℂ} (hF : F ∈ X.Sec q n)
    {γ : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L) (v : Fin n → Vsp X.dim) :
    X.ptN2 q F (v + γ) = X.ptN2 q F v := by
  unfold PT.ptN2
  rw [hF.2 γ hγ v]
  set z : ℂ := (q : ℂ) * Real.pi * HC v γ + q * Real.pi * HC γ γ / 2 with hz
  have hre : 2 * z.re + (-(q * Real.pi) * (HC (v + γ) (v + γ)).re) = -(q * Real.pi) * (HC v v).re := by
    rw [hz, nA_re_S, nA_HC_add_add_re]; ring
  rw [norm_mul, norm_mul, norm_pow, nA_epsprod_norm X hγ, one_pow, one_mul, Complex.norm_exp,
    mul_pow, ← hre, Real.exp_add, sq (Real.exp z.re), ← Real.exp_add]
  ring_nf
end ReciprocityTheory.ChartRestriction.G.I2
