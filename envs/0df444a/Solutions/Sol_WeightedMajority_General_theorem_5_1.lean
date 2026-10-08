-- Prove2me | solution 1 for WeightedMajority.General.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:04:09.106496+00:00
-- url     : https://prove2.me/submissions/b4199a4d-b355-4bdd-94d3-6c2f435389ad

import Mathlib
import Definitions.Def_WeightedMajority_General_WMGRun
open WeightedMajority.General

private theorem mistake_step {n T : ℕ} {β : ℝ} {x : Fin T → Fin n → ℝ} {ρ : Fin T → ℝ}
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



theorem solution {n T : ℕ} {β : ℝ} {x : Fin T → Fin n → ℝ} {ρ : Fin T → ℝ}
    {w : ℕ → Fin n → ℝ} {pred : Fin T → ℝ} {upd : Fin T → Bool} {F : Fin T → Fin n → ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hrun : IsWMGRun β x ρ w pred upd F)
    (hfin : 0 < WeightedMajority.Basic.totalWeight w T) :
    (mistakeCount pred ρ : ℝ) ≤
      Real.log (WeightedMajority.Basic.totalWeight w 0 / WeightedMajority.Basic.totalWeight w T) / Real.log (2 / (1 + β)) := by
  classical
  let c : ℝ := (1 + β) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hc1 : c < 1 := by dsimp [c]; linarith
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
  have hstep (k : Fin T) : WeightedMajority.Basic.totalWeight w (k.val + 1) ≤
      (if pred k ≠ ρ k then c else 1) * WeightedMajority.Basic.totalWeight w k.val := by
    split_ifs with h
    · exact mistake_step hβ0 hβ1 hrun k h
    · rw [one_mul]
      unfold WeightedMajority.Basic.totalWeight
      apply Finset.sum_le_sum
      intro i hi
      cases hu : upd k with
      | false => rw [hrun.no_update k i hu]
      | true =>
        rw [hrun.update k i hu]
        have hf := hrun.factor_upper k i hu
        have hf1 : F k i ≤ 1 := by nlinarith [abs_nonneg (x k i - ρ k)]
        simpa using mul_le_mul_of_nonneg_right hf1 (hw k.val (by omega) i)
  let f := fun k : Fin T => if pred k ≠ ρ k then c else 1
  have hb : ∀ t, t ≤ T → WeightedMajority.Basic.totalWeight w t ≤
      WeightedMajority.Basic.totalWeight w 0 * ∏ k ∈ Finset.univ.filter (fun k : Fin T => k.val < t), f k := by
    intro t
    induction t with
    | zero => intro ht; simp
    | succ t ih =>
      intro ht
      let k : Fin T := ⟨t, by omega⟩
      have he : Finset.univ.filter (fun k : Fin T => k.val < t + 1) =
          insert k (Finset.univ.filter (fun k : Fin T => k.val < t)) := by
        ext a; simp [k, Fin.ext_iff]; omega
      rw [he, Finset.prod_insert (by simp [k])]
      have hh := mul_le_mul_of_nonneg_left (ih (by omega))
        (show 0 ≤ f k by dsimp [f]; split_ifs <;> positivity)
      have hs := hstep k
      change _ ≤ f k * _ at hs
      nlinarith only [hh, hs]
  have hbT := hb T le_rfl
  have he : (Finset.univ.filter (fun k : Fin T => k.val < T)) = Finset.univ := by
    ext k; simp [k.isLt]
  rw [he] at hbT
  have hp : (∏ k : Fin T, f k) = c ^ mistakeCount pred ρ := by
    simp [f, mistakeCount, Finset.prod_ite, Finset.prod_const]
  rw [hp] at hbT
  have hs0 : 0 < WeightedMajority.Basic.totalWeight w 0 := by
    apply Finset.sum_pos
    · intro i hi; exact hrun.initial_pos i
    · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hrun.pool_nonempty)
  have hlog := Real.log_le_log hfin hbT
  rw [Real.log_mul hs0.ne' (pow_pos hc _).ne', Real.log_pow] at hlog
  have hden : 0 < Real.log (2 / (1 + β)) := by
    apply Real.log_pos
    apply (one_lt_div (by linarith)).mpr
    linarith
  have hneg : Real.log (2 / (1 + β)) = -Real.log c := by
    rw [show 2 / (1 + β) = c⁻¹ by dsimp [c]; field_simp]
    exact Real.log_inv c
  apply (le_div_iff₀ hden).mpr
  rw [Real.log_div hs0.ne' hfin.ne', hneg]
  linarith

#print axioms solution

