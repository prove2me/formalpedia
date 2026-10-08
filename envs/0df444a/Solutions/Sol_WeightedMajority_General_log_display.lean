-- Prove2me | solution 1 for WeightedMajority.General.log_display
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:04:30.676672+00:00
-- url     : https://prove2.me/submissions/c2804717-8fef-411d-8977-d9fda3892e17

import Mathlib
import Definitions.Def_WeightedMajority_General_WMGRun

open WeightedMajority.General

theorem solution {n T : ℕ} {β : ℝ} {x : Fin T → Fin n → ℝ} {ρ : Fin T → ℝ}
    {w : ℕ → Fin n → ℝ} {pred : Fin T → ℝ} {upd : Fin T → Bool} {F : Fin T → Fin n → ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hrun : IsWMGRun β x ρ w pred upd F)
    (hnot : ¬ (β = 0 ∧ ∃ k, upd k = true ∧ |gamma x w k - ρ k| = 1)) :
    (∑ k ∈ Finset.univ.filter (fun k => upd k = true),
        Real.log (1 - (1 - β) * |gamma x w k - ρ k|)) ≤
      (∑ k ∈ Finset.univ.filter (fun k => upd k = true ∧ pred k ≠ ρ k),
        Real.log (1 - (1 - β) * |gamma x w k - ρ k|)) ∧
    (∑ k ∈ Finset.univ.filter (fun k => upd k = true ∧ pred k ≠ ρ k),
        Real.log (1 - (1 - β) * |gamma x w k - ρ k|)) ≤
      (mistakeCount pred ρ : ℝ) * Real.log (1 / 2 + 1 / 2 * β) := by
  classical
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
  have hg (k : Fin T) : 0 ≤ gamma x w k ∧ gamma x w k ≤ 1 := by
    have hs : 0 ≤ WeightedMajority.Basic.totalWeight w k.val :=
      Finset.sum_nonneg (fun i _ => hw k.val (by omega) i)
    have hn : 0 ≤ ∑ i, w k.val i * x k i :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hw k.val (by omega) i) (hrun.x_mem k i).1)
    have hu : (∑ i, w k.val i * x k i) ≤ WeightedMajority.Basic.totalWeight w k.val := by
      apply Finset.sum_le_sum
      intro i hi
      simpa using mul_le_mul_of_nonneg_left (hrun.x_mem k i).2 (hw k.val (by omega) i)
    unfold gamma
    refine ⟨div_nonneg hn hs, ?_⟩
    by_cases hz : WeightedMajority.Basic.totalWeight w k.val = 0
    · simp [hz]
    · exact (div_le_one (lt_of_le_of_ne hs (Ne.symm hz))).mpr hu
  have hab (k : Fin T) : |gamma x w k - ρ k| ≤ 1 := by
    rcases hrun.label_binary k with h | h <;> rw [h] <;> apply abs_le.mpr <;> constructor <;> linarith [(hg k).1, (hg k).2]
  have hpos (k : Fin T) (hu : upd k = true) : 0 < 1 - (1 - β) * |gamma x w k - ρ k| := by
    have h0 := abs_nonneg (gamma x w k - ρ k)
    have h1 := hab k
    have hn : 0 ≤ 1 - (1 - β) * |gamma x w k - ρ k| := by nlinarith
    by_contra h
    have he : β = 0 ∧ |gamma x w k - ρ k| = 1 := by
      have hz : 1 - (1 - β) * |gamma x w k - ρ k| = 0 := le_antisymm (le_of_not_gt h) hn
      constructor <;> nlinarith
    exact hnot ⟨he.1, k, hu, he.2⟩
  have hnon (k : Fin T) (hu : upd k = true) :
      Real.log (1 - (1 - β) * |gamma x w k - ρ k|) ≤ 0 := by
    apply Real.log_nonpos (hpos k hu).le
    nlinarith [abs_nonneg (gamma x w k - ρ k)]
  have hmis (k : Fin T) (h : pred k ≠ ρ k) : 1 / 2 ≤ |gamma x w k - ρ k| := by
    rcases hrun.label_binary k with hρ | hρ
    · have hp : pred k = 1 := (hrun.pred_binary k).resolve_left (by simpa [hρ] using h)
      have hγ : 1 / 2 ≤ gamma x w k := by
        by_contra hh
        have := hrun.pred_zero k (lt_of_not_ge hh)
        linarith
      rw [hρ, sub_zero, abs_of_nonneg (hg k).1]
      exact hγ
    · have hp : pred k = 0 := (hrun.pred_binary k).resolve_right (by simpa [hρ] using h)
      have hγ : gamma x w k ≤ 1 / 2 := by
        by_contra hh
        have := hrun.pred_one k (lt_of_not_ge hh)
        linarith
      rw [hρ, abs_of_nonpos (by linarith [(hg k).2])]
      linarith
  constructor
  · simp only [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro k hk
    by_cases hu : upd k = true
    · by_cases hm : pred k ≠ ρ k
      · simp [hu, hm]
      · simpa [hu, hm] using hnon k hu
    · simp [hu]
  · have he : Finset.univ.filter (fun k => upd k = true ∧ pred k ≠ ρ k) =
        Finset.univ.filter (fun k => pred k ≠ ρ k) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨And.right, fun h => ⟨hrun.upd_of_mistake k h, h⟩⟩
    rw [he]
    calc
      _ ≤ ∑ k ∈ Finset.univ.filter (fun k => pred k ≠ ρ k), Real.log (1 / 2 + 1 / 2 * β) := by
        apply Finset.sum_le_sum
        intro k hk
        have hm := (Finset.mem_filter.mp hk).2
        apply Real.log_le_log (hpos k (hrun.upd_of_mistake k hm))
        have hh := hmis k hm
        nlinarith
      _ = _ := by simp [mistakeCount]

#print axioms solution
