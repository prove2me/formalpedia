-- Prove2me | solution 1 for WeightedMajority.General.appendix_mistake_step
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:25:36.545117+00:00
-- url     : https://prove2.me/submissions/01e33713-c1af-468c-bd8d-b96bfcc08638

import Mathlib
import Definitions.Def_WeightedMajority_General_WMGRun
open WeightedMajority.General


/-- Appendix, p. 256 (alternate proof of Theorem 5.1): in a trial in which WMG makes a mistake,
the total weight after the update is at most `(1 + β) / 2` times the total weight before it. -/
theorem solution {n T : ℕ} {β : ℝ} {x : Fin T → Fin n → ℝ} {ρ : Fin T → ℝ}
    {w : ℕ → Fin n → ℝ} {pred : Fin T → ℝ} {upd : Fin T → Bool} {F : Fin T → Fin n → ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hrun : IsWMGRun β x ρ w pred upd F)
    (k : Fin T) (hmis : pred k ≠ ρ k) :
    WeightedMajority.Basic.totalWeight w (k.val + 1) ≤ (1 + β) / 2 * WeightedMajority.Basic.totalWeight w k.val := by
  have hw : ∀ t, t ≤ T → ∀ i, 0 ≤ w t i := by
    intro t
    induction t with
    | zero => intro ht i; exact (hrun.initial_pos i).le
    | succ t ih =>
      intro ht i
      let k : Fin T := ⟨t, by omega⟩
      have hi := ih (by omega) i
      cases hu : upd k with
      | false => simpa [k, hrun.no_update k i hu] using hi
      | true =>
        rw [hrun.update k i hu]
        exact mul_nonneg ((Real.rpow_nonneg hβ0 _).trans (hrun.factor_lower k i hu)) hi
  have hwk : ∀ i, 0 ≤ w k.val i := hw _ (by omega)
  have hs : 0 ≤ WeightedMajority.Basic.totalWeight w k.val := Finset.sum_nonneg (fun i _ => hwk i)
  have hu := hrun.upd_of_mistake k hmis
  have hstep : WeightedMajority.Basic.totalWeight w (k.val + 1) ≤
      WeightedMajority.Basic.totalWeight w k.val -
        (1 - β) * ∑ i, w k.val i * |x k i - ρ k| := by
    unfold WeightedMajority.Basic.totalWeight
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i hi
    rw [hrun.update k i hu]
    have hf := mul_le_mul_of_nonneg_right (hrun.factor_upper k i hu) (hwk i)
    nlinarith
  by_cases hz : WeightedMajority.Basic.totalWeight w k.val = 0
  · have hnon : 0 ≤ (1 - β) * ∑ i, w k.val i * |x k i - ρ k| := by
      apply mul_nonneg (by linarith)
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hwk i) (abs_nonneg _))
    rw [hz] at hstep ⊢
    linarith
  have hsp : 0 < WeightedMajority.Basic.totalWeight w k.val := lt_of_le_of_ne hs (Ne.symm hz)
  have hloss : WeightedMajority.Basic.totalWeight w k.val / 2 ≤
      ∑ i, w k.val i * |x k i - ρ k| := by
    rcases hrun.label_binary k with hρ | hρ
    · have hp : pred k = 1 := (hrun.pred_binary k).resolve_left (by simpa [hρ] using hmis)
      have hγ : 1 / 2 ≤ gamma x w k := by
        by_contra h
        have := hrun.pred_zero k (lt_of_not_ge h)
        linarith
      unfold gamma at hγ
      have := (le_div_iff₀ hsp).mp hγ
      simp only [hρ, sub_zero]
      simp_rw [abs_of_nonneg (hrun.x_mem k _).1]
      linarith
    · have hp : pred k = 0 := (hrun.pred_binary k).resolve_right (by simpa [hρ] using hmis)
      have hγ : gamma x w k ≤ 1 / 2 := by
        by_contra h
        have := hrun.pred_one k (lt_of_not_ge h)
        linarith
      unfold gamma at hγ
      have hsum := (div_le_iff₀ hsp).mp hγ
      have habs : ∀ i, |x k i - ρ k| = 1 - x k i := by
        intro i
        rw [hρ, abs_of_nonpos (by linarith [(hrun.x_mem k i).2])]
        ring
      simp_rw [habs, mul_sub, mul_one]
      rw [Finset.sum_sub_distrib]
      change WeightedMajority.Basic.totalWeight w k.val / 2 ≤
        WeightedMajority.Basic.totalWeight w k.val - _
      linarith
  have := mul_le_mul_of_nonneg_left hloss (show 0 ≤ 1 - β by linarith)
  nlinarith

#print axioms solution
