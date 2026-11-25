-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_ip_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:47:09.890161+00:00
-- url     : https://prove2.me/submissions/5df550bc-d63a-4f96-83b7-4104b6f23053

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_add_add_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_exp_mul_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_re_S
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_epsprod_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_epsprod_conj

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
theorem _root_.solution {q n : ℕ} {F G : (Fin n → Vsp X.dim) → ℂ} (hF : F ∈ X.Sec q n) (hG : G ∈ X.Sec q n)
    {γ : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L) (v : Fin n → Vsp X.dim) :
    F (v + γ) * (starRingEnd ℂ) (G (v + γ)) *
        ((Real.exp (-(q * Real.pi) * (HC (v + γ) (v + γ)).re) : ℝ) : ℂ) =
      F v * (starRingEnd ℂ) (G v) * ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ) := by
  rw [hF.2 γ hγ v, hG.2 γ hγ v]
  set e : ℂ := ∏ k, (X.eps (γ k) : ℂ) with he
  set z : ℂ := (q : ℂ) * Real.pi * HC v γ + q * Real.pi * HC γ γ / 2 with hz
  have hre : 2 * z.re + (-(q * Real.pi) * (HC (v + γ) (v + γ)).re) = -(q * Real.pi) * (HC v v).re := by
    rw [hz, nA_re_S, nA_HC_add_add_re]; ring
  have hee : e ^ q * (starRingEnd ℂ) (e ^ q) = 1 := by
    rw [map_pow, he, nA_epsprod_conj X, ← mul_pow, ← sq, nA_epsprod_sq X hγ, one_pow]
  calc e ^ q * cexp z * F v * (starRingEnd ℂ) (e ^ q * cexp z * G v) *
        ((Real.exp (-(q * Real.pi) * (HC (v + γ) (v + γ)).re) : ℝ) : ℂ)
      = (e ^ q * (starRingEnd ℂ) (e ^ q)) * (cexp z * (starRingEnd ℂ) (cexp z)) *
          (F v * (starRingEnd ℂ) (G v)) *
          ((Real.exp (-(q * Real.pi) * (HC (v + γ) (v + γ)).re) : ℝ) : ℂ) := by
        simp only [map_mul]; ring
    _ = _ := by
      rw [hee, nA_exp_mul_conj, ← hre, Real.exp_add, Complex.ofReal_mul]; ring
end ReciprocityTheory.ChartRestriction.G.I2
