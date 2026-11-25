-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paTh_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:30:53.066378+00:00
-- url     : https://prove2.me/submissions/2fce72e0-846c-4b5d-9352-2c1fbd7bc9f6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pa_factor

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
theorem _root_.solution (Y : GT ι) {q : ℕ}
    (hC : ∀ γ ∈ lat Y.b, ∀ γ' ∈ lat Y.b,
      Y.ka (γ + γ') = Y.ka γ * Y.ka γ' * cexp (-(Real.pi * q * (Hf γ γ').im) * I))
    {F : EuclideanSpace ℂ ι → ℂ} (hd : Differentiable ℂ (paTh Y q F))
    (hs : ∀ v, Summable (fun γ : lat Y.b => Y.ka γ * paU q γ F v)) :
    paTh Y q F ∈ Y.Sec q := by
  refine ⟨hd, fun γ hγ v => ?_⟩
  show ∑' γ' : lat Y.b, Y.ka γ' * paU q γ' F (v + γ) =
    Y.ka γ * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * ∑' γ' : lat Y.b, Y.ka γ' * paU q γ' F v
  rw [← (Equiv.addRight (⟨γ, hγ⟩ : lat Y.b)).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun γ'' => ?_
  obtain ⟨kk, hkk⟩ := Y.integral γ γ'' hγ γ''.2
  simp only [Equiv.coe_addRight, Submodule.coe_add, paU]
  rw [hC _ γ''.2 _ hγ]
  have hF : v + γ - ((γ'' : EuclideanSpace ℂ ι) + γ) = v - γ'' := by abel
  rw [hF]
  have hfac := pa_factor q v (γ'' : EuclideanSpace ℂ ι) γ kk hkk
  calc _ = Y.ka γ'' * Y.ka γ * (cexp (-(Real.pi * q * (Hf (γ'' : EuclideanSpace ℂ ι) γ).im) * I) *
        cexp (q * Real.pi * Hf (v + γ) ((γ'' : EuclideanSpace ℂ ι) + γ) -
          q * Real.pi * Hf ((γ'' : EuclideanSpace ℂ ι) + γ) ((γ'' : EuclideanSpace ℂ ι) + γ) / 2)) *
        F (v - γ'') := by ring
    _ = _ := by rw [hfac]; ring
end ReciprocityTheory.ChartRestriction.G.I2
