-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.boost_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:43:48.529099+00:00
-- url     : https://prove2.me/submissions/9cd7a5e1-5982-4dcd-9b9d-0956bc0c0919

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMinimumLowerBoundHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TwoSidedBoostBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoostLowerBounds_boost_lower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoostLowerBounds_plane_facts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RankOneBoostIsometries_boost_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds ImaginaryMajorants
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds
theorem _root_.solution (τ : X.Ψ) {z : Frame X.Ψ r} (hz : z ∈ X.dom) {e : Fin r → ℂ}
    (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) {σ : ℝ} (hσ : 0 < σ) (w : Fin r → ℂ) :
    X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w) ≤
      max (σ ^ 2) (σ ^ 2)⁻¹ * X.maj z τ w := by
  have hσ' : 0 < σ⁻¹ := inv_pos.2 hσ
  have ha : 0 < σ ^ 2 := by positivity
  have hl := BoostLowerBounds.boost_lower (X := X) (τ := τ) (z := z) hz hee he0 hσ'
    (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w)
  simp only [inv_inv] at hl
  obtain ⟨hm, hff, hef, hfe⟩ := BoostLowerBounds.plane_facts (X := X) (τ := τ) (z := z) hz hee he0
  rw [RankOneBoostIsometries.boost_comp X τ hm hee hff hef hfe hσ] at hl
  simp only [inv_pow, inv_inv] at hl
  have hmm : max (σ ^ 2) (σ ^ 2)⁻¹ * min (σ ^ 2)⁻¹ (σ ^ 2) = 1 := by
    rcases le_total (σ ^ 2) (σ ^ 2)⁻¹ with h | h
    · rw [max_eq_right h, min_eq_right h, inv_mul_cancel₀ ha.ne']
    · rw [max_eq_left h, min_eq_left h, mul_inv_cancel₀ ha.ne']
  have hM : 0 ≤ max (σ ^ 2) (σ ^ 2)⁻¹ := le_max_of_le_left ha.le
  calc X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w)
      = max (σ ^ 2) (σ ^ 2)⁻¹ * (min (σ ^ 2)⁻¹ (σ ^ 2) *
          X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w)) := by
        rw [← mul_assoc, hmm, one_mul]
    _ ≤ max (σ ^ 2) (σ ^ 2)⁻¹ * X.maj z τ w := mul_le_mul_of_nonneg_left hl hM
end ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds
