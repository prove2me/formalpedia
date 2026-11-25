-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:35.872218+00:00
-- url     : https://prove2.me/submissions/38a532e7-83c6-41b9-84b0-2780c9591f1b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pbwt_pos
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_dom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (a : ℂ) (ha : a = Complex.I ∨ a = -Complex.I) (lam : Fin n → ℝ) (c₀ : ℝ) (hc : 0 ≤ c₀)
    (hc₀ : (n : ℝ) * c₀ ≤ 1 / 4) (b : Mc n)
    (hb : ∀ i j, ‖b i j - Matrix.diagonal (fun i => (lam i : ℂ)) i j‖ ≤ c₀ * (pbwt lam i * pbwt lam j)) :
    IsUnit (1 - a • b).det ∧ (∀ i j, ‖(1 - a • b)⁻¹ i j‖ ≤ 3 / (pbwt lam i * pbwt lam j)) := by
  have hdet : IsUnit (1 - a • b).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    funext i
    have := pb_dom a ha lam c₀ hc hc₀ b hb v 0 (fun i => by simp [hv]) i
    have hw := pbwt_pos lam i
    have : ‖v i‖ ≤ 0 := by nlinarith [norm_nonneg (v i)]
    simpa using le_antisymm this (norm_nonneg _)
  refine ⟨hdet, fun i j => ?_⟩
  set Y := 1 - a • b
  have hx : Y *ᵥ (Y⁻¹ *ᵥ Pi.single j 1) = Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hwj := pbwt_pos lam j
  have key := pb_dom a ha lam c₀ hc hc₀ b hb (Y⁻¹ *ᵥ Pi.single j 1) (1 / pbwt lam j) (fun k => by
    rw [hx]
    by_cases hk : k = j
    · subst hk; simp [inv_mul_cancel₀ hwj.ne']
    · simp [Pi.single_apply, hk]; exact mul_nonneg (by positivity) (pbwt_pos lam k).le) i
  have e : (Y⁻¹ *ᵥ Pi.single j 1) i = Y⁻¹ i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e] at key
  have hwi := pbwt_pos lam i
  rw [le_div_iff₀ (mul_pos hwi hwj)]
  calc ‖Y⁻¹ i j‖ * (pbwt lam i * pbwt lam j) = (pbwt lam i * ‖Y⁻¹ i j‖) * pbwt lam j := by ring
    _ ≤ (3 * (1 / pbwt lam j)) * pbwt lam j := mul_le_mul_of_nonneg_right key hwj.le
    _ = 3 := by field_simp
end PositivityTheory.Rg.Sw.WR.K.GB
