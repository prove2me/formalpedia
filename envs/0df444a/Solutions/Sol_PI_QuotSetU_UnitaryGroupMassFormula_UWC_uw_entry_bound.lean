-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.UWC.uw_entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:40.65385+00:00
-- url     : https://prove2.me/submissions/11a63e44-ddd1-4c44-b1ae-fa8dca8d0f3c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_star_dotProduct_Hpk_mulVec_eq_sum_sub
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_star_mul_self_eq
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_tz_eq
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_herm_invariant
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_norm_bvec_le
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_norm_H_bvec_le
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mulVec_bvec_apply
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_uw_block


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.UWC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.UWC
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (i j : Fin (2 * r + k + 1)) : ‖h i j‖ ≤ Bd k r z := by
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  set A := ∑ i ∈ Wp k r, ‖z i‖ ^ 2 with hAdef
  set a := Real.sqrt A with hadef
  set b := ‖z (lI k r)‖ with hbdef
  set Z := ∑ i, ‖z i‖ with hZdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have haa : a ^ 2 = A := Real.sq_sqrt hA0
  have hTab : Tz k r z = b ^ 2 - a ^ 2 := by rw [tz_eq hz, haa]
  have hab : a < b := by
    by_contra hc
    push Not at hc
    nlinarith [mul_self_le_mul_self hb0 hc]
  have hba : 0 < b - a := by linarith
  have hq0 : 0 ≤ (a * n + Z) / (b - a) := div_nonneg (by positivity) hba.le
  have hBd : Bd k r z = n + (a * n + Z) / (b - a) := rfl
  rw [hBd]
  have hδ : ∀ x : ℂ, (x = if i = j then 1 else 0) → ‖x‖ ≤ n + (a * n + Z) / (b - a) := by
    intro x hx
    have : ‖x‖ ≤ 1 := by rw [hx]; split_ifs <;> simp
    linarith
  by_cases hij : inW k r i ∧ inW k r j
  swap
  · exact hδ _ (uw_block hh i j hij)
  obtain ⟨hiW, hjW⟩ := hij

  set c : Fin (2 * r + k + 1) → ℂ := fun x => h x j with hcdef
  have hc : c = h *ᵥ bvec j := funext fun x => (mulVec_bvec_apply h x j).symm
  have hcW : ∀ x, ¬ inW k r x → c x = 0 := by
    intro x hx
    have hne : x ≠ j := by rintro rfl; exact hx hjW
    have := uw_block hh x j (fun h' => hx h'.1)
    simp only [hcdef, this, if_neg hne]
  have hEA : star c ⬝ᵥ (Hpk k r *ᵥ c) = star (bvec j) ⬝ᵥ (Hpk k r *ᵥ bvec j) := by
    rw [hc]; exact herm_invariant hh.1 _ _
  have hEK : star z ⬝ᵥ (Hpk k r *ᵥ c) = star z ⬝ᵥ (Hpk k r *ᵥ bvec j) := by
    have := herm_invariant hh.1 z (bvec j)
    rw [hh.2.2] at this
    rw [hc]; exact this
  have hnA : ‖star (bvec j) ⬝ᵥ (Hpk k r *ᵥ bvec j)‖ ≤ n := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ x ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))),
        ‖(star (bvec j)) x * (Hpk k r *ᵥ bvec j) x‖ ≤ 1 := by
      intro x _
      rw [norm_mul, Pi.star_apply, norm_star]
      exact mul_le_one₀ (norm_bvec_le _ _) (norm_nonneg _) (norm_H_bvec_le _ _)
    refine (Finset.sum_le_sum this).trans ?_
    simp [hn]
  have hnK : ‖star z ⬝ᵥ (Hpk k r *ᵥ bvec j)‖ ≤ Z := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, Pi.star_apply, norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_H_bvec_le _ _)
  rw [star_dotProduct_Hpk_mulVec_eq_sum_sub c c hcW] at hEA
  rw [star_dotProduct_Hpk_mulVec_eq_sum_sub c z hcW] at hEK
  set X2 := ∑ x ∈ Wp k r, ‖c x‖ ^ 2 with hX2
  set Y := ‖c (lI k r)‖ with hY
  have hY0 : 0 ≤ Y := norm_nonneg _
  have hX20 : 0 ≤ X2 := Finset.sum_nonneg fun _ _ => sq_nonneg _

  have h1 : X2 - Y ^ 2 ≤ n := by
    have e := congrArg Complex.re hEA
    simp only [star_mul_self_eq] at e
    rw [← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re] at e
    rw [e]
    exact (Complex.re_le_norm _).trans hnA

  have h2 : b * Y ≤ (∑ x ∈ Wp k r, ‖z x‖ * ‖c x‖) + Z := by
    have e : star (z (lI k r)) * c (lI k r) =
        (∑ x ∈ Wp k r, star (z x) * c x) - star z ⬝ᵥ (Hpk k r *ᵥ bvec j) := by
      rw [← hEK]; ring
    have e2 := congrArg norm e
    rw [norm_mul, norm_star] at e2
    rw [hbdef, hY, e2]
    refine (norm_sub_le _ _).trans (add_le_add ?_ hnK)
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_mul, norm_star]
  have hCS : (∑ x ∈ Wp k r, ‖z x‖ * ‖c x‖) ≤ a * Real.sqrt X2 :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hsX : Real.sqrt X2 ≤ n + Y := by
    have : X2 ≤ (n + Y) ^ 2 := by nlinarith
    calc Real.sqrt X2 ≤ Real.sqrt ((n + Y) ^ 2) := Real.sqrt_le_sqrt this
      _ = n + Y := Real.sqrt_sq (by linarith)
  have hYb : Y ≤ (a * n + Z) / (b - a) := by
    rw [le_div_iff₀ hba]
    nlinarith
  by_cases hil : i = lI k r
  · have : ‖h i j‖ = Y := by rw [hY, hil]
    rw [this]; linarith
  · have hiWp : i ∈ Wp k r := by
      unfold Wp inW at *
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hiW.1, ?_⟩
      rcases Nat.lt_or_ge i.val (r + k) with h' | h'
      · exact h'
      · exact absurd (Fin.ext (by simp [lI]; omega)) hil
    have hci : ‖c i‖ ^ 2 ≤ X2 :=
      Finset.single_le_sum (f := fun x => ‖c x‖ ^ 2) (fun _ _ => sq_nonneg _) hiWp
    have hci' : ‖c i‖ ≤ n + Y := by
      have h0 : 0 ≤ ‖c i‖ := norm_nonneg _
      nlinarith
    have : ‖h i j‖ = ‖c i‖ := rfl
    rw [this]; linarith
end PI.QuotSetU.UnitaryGroupMassFormula.UWC
