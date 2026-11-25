-- Prove2me | solution 1 for PI.VolStabW.FFHS.card_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:18:43.928163+00:00
-- url     : https://prove2.me/submissions/5c001193-7dcf-414c-9bff-d76365e0b39f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFHS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFCnt
import Theorems.Thm_PI_VolStabW_FFHS_card_decomp
import Theorems.Thm_PI_VolStabW_FFHS_IsSq_self_fixed
import Theorems.Thm_PI_VolStabW_FFHS_IsSq_zero_left
import Theorems.Thm_PI_VolStabW_FFHS_exists_aniso
import Theorems.Thm_PI_VolStabW_FFHS_finrank_perp
import Theorems.Thm_PI_VolStabW_FFHS_perp_isHS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
namespace PI.VolStabW.FFHS
theorem _root_.solution (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : K) ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ c, σ c = c →
      (Nat.card {x : V // h x x = c} : ℝ) = (q : ℝ) ^ (2 * (m : ℤ) - 1) +
        (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * ((if c = 0 then (q : ℝ) else 0) - 1) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
  intro m
  induction m with
  | zero =>
    intro V _ _ _ h hs hm c _
    have : Subsingleton V := Module.finrank_zero_iff.1 hm
    by_cases hc : c = 0
    · have h1 : Nat.card {x : V // h x x = c} = 1 := Nat.card_eq_one_iff_exists.2
        ⟨⟨0, by rw [hs.toIsSq.zero_left, hc]⟩, fun y => Subtype.ext (Subsingleton.elim _ _)⟩
      rw [h1, if_pos hc]
      simp only [Nat.cast_one, CharP.cast_eq_zero, mul_zero, zero_sub, pow_zero, one_mul]
      rw [zpow_neg_one, ← mul_one_add, add_sub_cancel, inv_mul_cancel₀ hq']
    · have : IsEmpty {x : V // h x x = c} := ⟨fun ⟨x, hx⟩ => hc (by
        rw [← hx, Subsingleton.elim x 0, hs.toIsSq.zero_left])⟩
      rw [Nat.card_of_isEmpty, if_neg hc]
      simp
  | succ m ih =>
    intro V _ _ _ h hs hm c hc
    have hq := hs.toIsSq
    have : Finite V := Module.finite_of_finite K
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hm
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨e, he⟩ := exists_aniso h2 hs x hx
    have hfr : finrank K (perp hq e) = m := by have := finrank_perp hq e he; omega
    rw [card_decomp hq e he c, Nat.cast_sum]
    have hfix : ∀ t : K, σ (c - σ t * t * h e e) = c - σ t * t * h e e := fun t => by
      rw [map_sub, map_mul, map_mul, hσ, hc, hq.self_fixed]; ring
    rw [Finset.sum_congr rfl (fun t _ => ih (perp hq e) (fun w w' => h w w')
      (perp_isHS hs e he) hfr _ (hfix t))]
    have hcnt : ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) =
        if c = 0 then 1 else (q : ℝ) + 1 := by
      have e1 : (Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card =
          Nat.card {t : K // t * σ t = c * (h e e)⁻¹} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        congr 1
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [eq_mul_inv_iff_mul_eq₀ he]
        constructor <;> intro H <;> linear_combination -H
      have hf : σ (c * (h e e)⁻¹) = c * (h e e)⁻¹ := by
        rw [map_mul, map_inv₀, hc, hq.self_fixed]
      rw [e1, hN _ hf]
      by_cases hc0 : c = 0
      · simp [hc0]
      · have : c * (h e e)⁻¹ ≠ 0 := mul_ne_zero hc0 (inv_ne_zero he)
        simp [hc0, this]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hK, ← Finset.mul_sum,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hK, Finset.sum_ite,
      Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      nsmul_eq_mul, hcnt]
    have e1 : (q : ℝ) ^ (2 * ((m + 1 : ℕ) : ℤ) - 1) = (q : ℝ) ^ (2 * (m : ℤ) - 1) * q ^ 2 := by
      rw [show 2 * ((m + 1 : ℕ) : ℤ) - 1 = (2 * m - 1) + 2 by push_cast; ring, zpow_add₀ hq']
      norm_cast
    have e2 : (q : ℝ) ^ (((m + 1 : ℕ) : ℤ) - 1) = (q : ℝ) ^ ((m : ℤ) - 1) * q := by
      rw [show ((m + 1 : ℕ) : ℤ) - 1 = ((m : ℤ) - 1) + 1 by push_cast; ring, zpow_add₀ hq',
        zpow_one]
    rw [e1, e2, pow_succ]
    by_cases hc0 : c = 0
    · simp only [hc0, if_true]; push_cast; ring
    · simp only [hc0, if_false]; push_cast; ring
end PI.VolStabW.FFHS
