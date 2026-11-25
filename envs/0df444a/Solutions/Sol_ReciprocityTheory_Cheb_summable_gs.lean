-- Prove2me | solution 1 for ReciprocityTheory.Cheb.summable_gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:56.309855+00:00
-- url     : https://prove2.me/submissions/829d7b4e-613d-4e6d-b31f-4f59131c58da

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_NormGsEmbZLe
import Theorems.Thm_ReciprocityTheory_Cheb_norm_gs_le
import Theorems.Thm_ReciprocityTheory_Cheb_exists_support_bound
import Theorems.Thm_ReciprocityTheory_Cheb_uphi_le_one
import Theorems.Thm_ReciprocityTheory_Cheb_uphi_of_norm_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {l : ℕ} (χ : DirichletCharacter ℂ l) (Λ : Submodule ℤ (mixedSpace E)) [DiscreteTopology Λ]
    (hΛ : Module.finrank ℤ Λ = Module.finrank ℚ E) {s : ℝ} (hs : 1 < s) :
    Summable fun x : Λ => Gs χ s (x : mixedSpace E) := by
  obtain ⟨c₀, hc₀, -, hb⟩ := exists_support_bound (E := E)
  set d := Module.finrank ℚ E
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Module.finrank_pos
  set r : ℝ := -((d : ℝ) * s)
  have hr : r < -(Module.finrank ℤ Λ : ℝ) := by
    rw [hΛ]; simp only [r, neg_lt_neg_iff]; nlinarith
  refine Summable.of_norm_bounded ((ZLattice.summable_norm_rpow Λ r hr).mul_left (c₀ ^ r)) fun x => ?_
  refine (norm_gs_le χ s _).trans ?_
  have hpos : 0 ≤ c₀ ^ r * ‖x‖ ^ r := mul_nonneg (Real.rpow_nonneg hc₀.le _) (Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hu : uphi (x : mixedSpace E) = 0
  · rw [hu, zero_mul]; exact hpos
  obtain ⟨-, hN⟩ := hb _ hu
  have hN0 : mixedEmbedding.norm (x : mixedSpace E) ≠ 0 := by
    intro h; exact hu (uphi_of_norm_eq_zero h)
  have hx0 : (x : mixedSpace E) ≠ 0 := by
    rintro h; apply hN0; rw [h]
    exact mixedEmbedding.norm_eq_zero_iff.mpr ⟨Classical.arbitrary _, by simp⟩
  have hxn : 0 < ‖(x : mixedSpace E)‖ := norm_pos_iff.mpr hx0
  have hcx : 0 < c₀ * ‖(x : mixedSpace E)‖ := mul_pos hc₀ hxn
  have key : (mixedEmbedding.norm (x : mixedSpace E)) ^ (-s) ≤ (c₀ * ‖(x : mixedSpace E)‖) ^ r := by
    have : (c₀ * ‖(x : mixedSpace E)‖) ^ r = ((c₀ * ‖(x : mixedSpace E)‖) ^ d) ^ (-s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hcx.le]; simp [r]
    rw [this]
    exact Real.rpow_le_rpow_of_nonpos (pow_pos hcx _) (by rw [mul_pow]; exact hN) (by linarith)
  calc uphi (x : mixedSpace E) * (mixedEmbedding.norm (x : mixedSpace E)) ^ (-s)
      ≤ 1 * (c₀ * ‖(x : mixedSpace E)‖) ^ r :=
        mul_le_mul (uphi_le_one _) key (Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _) zero_le_one
    _ = c₀ ^ r * ‖x‖ ^ r := by rw [one_mul, Real.mul_rpow hc₀.le (norm_nonneg _)]; rfl
end ReciprocityTheory.Cheb
