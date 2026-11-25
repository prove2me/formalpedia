-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paTail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:27:25.576375+00:00
-- url     : https://prove2.me/submissions/a8072879-0dc4-493f-8565-63592915f31c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfEqInner
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paCount

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
theorem _root_.solution (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2) :
    Summable (fun γ : lat Y.b => if (γ : EuclideanSpace ℂ ι) = 0 then 0 else
      Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16)) ∧
    ∑' γ : lat Y.b, (if (γ : EuclideanSpace ℂ ι) = 0 then 0 else
      Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16)) ≤
      2 * 9 ^ Fintype.card ι * Real.exp (-R0 ^ 2 / 16) := by
  set s : Set (lat Y.b) := {γ : lat Y.b | (γ : EuclideanSpace ℂ ι) ≠ 0} with hs
  let f : lat Y.b → ℝ := fun γ => Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16)
  have hfun : (fun γ : lat Y.b => if (γ : EuclideanSpace ℂ ι) = 0 then 0 else
      Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16)) = s.indicator f := by
    funext γ
    by_cases h0 : (γ : EuclideanSpace ℂ ι) = 0
    · have : γ ∉ s := fun h => h h0
      rw [if_pos h0, Set.indicator_of_notMem this]
    · have : γ ∈ s := h0
      rw [if_neg h0, Set.indicator_of_mem this]
  have hqpi : (0 : ℝ) ≤ q * Real.pi := by positivity
  have hh : ∀ i : s, Real.exp (-(Real.sqrt (q * Real.pi) * ‖((i : lat Y.b) : EuclideanSpace ℂ ι)‖) ^ 2 / 16) =
      f i := by
    intro i
    simp only [f]
    congr 1
    rw [mul_pow, Real.sq_sqrt hqpi]
    ring
  obtain ⟨hsum, hle⟩ := hA s (fun i => Real.sqrt (q * Real.pi) * ‖((i : lat Y.b) : EuclideanSpace ℂ ι)‖)
    (Fintype.card ι) R0 hR0 hR (fun i => hlat _ (i : lat Y.b).2 i.2)
    (fun R hR' S hS => paCount hP Y hR0 hlat R hR' S hS)
  simp only [hh] at hsum hle
  rw [hfun]
  refine ⟨(summable_subtype_iff_indicator).1 hsum, ?_⟩
  rw [← tsum_subtype]
  exact hle
end ReciprocityTheory.ChartRestriction.G.I2.FPw
