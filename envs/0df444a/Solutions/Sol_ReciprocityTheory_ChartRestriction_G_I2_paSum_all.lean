-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paSum_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:45:27.594625+00:00
-- url     : https://prove2.me/submissions/479697c5-fb3f-45a0-b055-8174af12b0f4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paTail
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paTail


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
theorem _root_.solution (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2) :
    Summable (fun γ : lat Y.b => Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16)) := by
  obtain ⟨hT, -⟩ := paTail hP hA Y hq hR0 hlat hR
  have h0 : Summable (fun γ : lat Y.b => if (γ : EuclideanSpace ℂ ι) = 0 then (1 : ℝ) else 0) := by
    refine summable_of_ne_finset_zero (s := {0}) fun γ hγ => ?_
    have : (γ : EuclideanSpace ℂ ι) ≠ 0 := by
      intro h; apply hγ; rw [Finset.mem_singleton]; exact Subtype.ext h
    simp [this]
  refine (hT.add h0).congr fun γ => ?_
  by_cases h : (γ : EuclideanSpace ℂ ι) = 0
  · simp [h]
  · simp [h]
end ReciprocityTheory.ChartRestriction.G.I2
