-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds.boost_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:57.222925+00:00
-- url     : https://prove2.me/submissions/46c889f3-1c1e-470d-931f-19ad2aeafd86

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RankOneBoostIsometries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoostLowerBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoostLowerBounds_plane_facts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoostLowerBounds_maj_decomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_maj_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RankOneBoostIsometries_boost_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace BoostLowerBounds
open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries
variable {r : ℕ} (X : Data E r) (τ : X.Ψ) {z : Frame X.Ψ r} (hz : z ∈ X.dom) {e : Fin r → ℂ}
include hz
private theorem hermC_Gm_sub_left (u u' v : Fin r → ℂ) :
    hermC τ.1 X.Gm (u - u') v = hermC τ.1 X.Gm u v - hermC τ.1 X.Gm u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
private theorem hermC_Gm_smul_left (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (c • u) v = c * hermC τ.1 X.Gm u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
end BoostLowerBounds
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds
open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries
variable {r : ℕ} (X : Data E r) (τ : X.Ψ) {z : Frame X.Ψ r} (hz : z ∈ X.dom) {e : Fin r → ℂ}
include hz
namespace ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds
theorem _root_.solution (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    (w : Fin r → ℂ) :
    min (σ ^ 2) (σ ^ 2)⁻¹ * X.maj z τ w ≤
      X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w) := by
  obtain ⟨hm, hff, hef, hfe⟩ := plane_facts X τ hz hee he0
  have hm0 : ((X.maj z τ e : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  have hσ0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A = hermC τ.1 X.Gm w (X.jp z τ e) / (X.maj z τ e : ℂ) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℂ, B = hermC τ.1 X.Gm w e / (X.maj z τ e : ℂ) := ⟨_, rfl⟩
  have hwf : hermC τ.1 X.Gm w (X.jp z τ e) = A * X.maj z τ e := by
    rw [hA, div_mul_cancel₀ _ hm0]
  have hwe : hermC τ.1 X.Gm w e = B * X.maj z τ e := by
    rw [hB, div_mul_cancel₀ _ hm0]
  have h0e : hermC τ.1 X.Gm (w - A • e - B • X.jp z τ e) e = 0 := by
    rw [hermC_Gm_sub_left X τ hz, hermC_Gm_sub_left X τ hz, hermC_Gm_smul_left X τ hz, hermC_Gm_smul_left X τ hz, hee, hfe,
      hwe]
    ring
  have h0f : hermC τ.1 X.Gm (w - A • e - B • X.jp z τ e) (X.jp z τ e) = 0 := by
    rw [hermC_Gm_sub_left X τ hz, hermC_Gm_sub_left X τ hz, hermC_Gm_smul_left X τ hz, hermC_Gm_smul_left X τ hz, hef, hff,
      hwf]
    ring
  have hw : w = (w - A • e - B • X.jp z τ e) + A • e + B • X.jp z τ e := by abel
  have hBw : Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w =
      (w - A • e - B • X.jp z τ e) + ((σ : ℂ)⁻¹ * A) • e + ((σ : ℂ) * B) • X.jp z τ e := by
    rw [boost_mulVec, hwf, hwe]
    have c1 : (((σ⁻¹ - 1) / X.maj z τ e : ℝ) : ℂ) * (A * (X.maj z τ e : ℂ)) =
        (σ : ℂ)⁻¹ * A - A := by
      push_cast
      field_simp
    have c2 : (((σ⁻¹⁻¹ - 1) / X.maj z τ e : ℝ) : ℂ) * (B * (X.maj z τ e : ℂ)) =
        (σ : ℂ) * B - B := by
      rw [inv_inv]
      push_cast
      field_simp
    rw [c1, c2, sub_smul, sub_smul]
    abel
  have hmw : X.maj z τ w = X.maj z τ (w - A • e - B • X.jp z τ e) +
      (Complex.normSq A + Complex.normSq B) * X.maj z τ e := by
    rw [← maj_decomp X τ hz hee he0 _ h0e h0f A B, ← hw]
  rw [hBw, maj_decomp X τ hz hee he0 _ h0e h0f, hmw]
  simp only [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal]
  have hM0 := MajorantConjugateTransfer.maj_nonneg (X := X) hz τ (w - A • e - B • X.jp z τ e)
  have hNA := Complex.normSq_nonneg A
  have hNB := Complex.normSq_nonneg B
  have hs0 : 0 < σ * σ := mul_pos hσ hσ
  rw [sq]
  have hk2 : min (σ * σ) (σ * σ)⁻¹ ≤ σ * σ := min_le_left _ _
  have hk3 : min (σ * σ) (σ * σ)⁻¹ ≤ (σ * σ)⁻¹ := min_le_right _ _
  have hk1 : min (σ * σ) (σ * σ)⁻¹ ≤ 1 := by
    rcases le_total (σ * σ) 1 with h | h
    · exact hk2.trans h
    · refine hk3.trans ?_
      have hi : (σ * σ)⁻¹ * (σ * σ) = 1 := inv_mul_cancel₀ hs0.ne'
      have hip : 0 < (σ * σ)⁻¹ := inv_pos.mpr hs0
      nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hk1 hM0,
    mul_le_mul_of_nonneg_right hk3 (mul_nonneg hNA hm.le),
    mul_le_mul_of_nonneg_right hk2 (mul_nonneg hNB hm.le)]
end ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds
