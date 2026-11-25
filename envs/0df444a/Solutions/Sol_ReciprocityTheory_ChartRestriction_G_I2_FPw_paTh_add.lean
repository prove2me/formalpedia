-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paTh_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:29.112883+00:00
-- url     : https://prove2.me/submissions/f5f43d44-74d9-4467-9903-5bd62976f98c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_conj_eq_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution {Y : GT ι} {q : ℕ} (hC : Coc Y q) (F : EuclideanSpace ℂ ι → ℂ)
    {γ : EuclideanSpace ℂ ι} (hγ : γ ∈ lat Y.b) (v : EuclideanSpace ℂ ι) :
    paTh Y q F (v + γ) = Y.ka γ * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * paTh Y q F v := by
  simp only [paTh]
  rw [← (Equiv.addLeft (⟨γ, hγ⟩ : lat Y.b)).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun δ => ?_
  simp only [Equiv.coe_addLeft, Submodule.coe_add, paU]
  rw [hC γ hγ δ δ.2]
  have hF : v + γ - (γ + (δ : EuclideanSpace ℂ ι)) = v - δ := by abel
  rw [hF]
  have hexp : cexp (-(Real.pi * q * (Hf γ (δ : EuclideanSpace ℂ ι)).im) * I) *
      cexp (q * Real.pi * Hf (v + γ) (γ + (δ : EuclideanSpace ℂ ι)) -
        q * Real.pi * Hf (γ + (δ : EuclideanSpace ℂ ι)) (γ + (δ : EuclideanSpace ℂ ι)) / 2) =
      cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) *
        cexp (q * Real.pi * Hf v (δ : EuclideanSpace ℂ ι) -
          q * Real.pi * Hf (δ : EuclideanSpace ℂ ι) (δ : EuclideanSpace ℂ ι) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [Hf_add_left, Hf_add_right, Hf_add_right, Hf_add_left, Hf_add_right, Hf_add_right]
    have hc := conj_eq_sub (Hf γ (δ : EuclideanSpace ℂ ι))
    rw [Hf_conj] at hc
    rw [hc]
    ring
  linear_combination (Y.ka γ * Y.ka δ * F (v - δ)) * hexp
end ReciprocityTheory.ChartRestriction.G.I2.FPw
