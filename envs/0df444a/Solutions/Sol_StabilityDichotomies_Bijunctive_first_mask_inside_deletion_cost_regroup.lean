-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.first_mask_inside_deletion_cost_regroup
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:43:13.860417+00:00
-- url     : https://prove2.me/submissions/d94f72b4-dbbc-4a27-988c-312bddf6461a

import Theorems.Thm_StabilityDichotomies_Bijunctive_first_mask_single_flip_probability_balance
noncomputable section
open scoped Classical BigOperators
open Function MeasureTheory ProbabilityTheory Set StabilityDichotomies.Bijunctive

private def maskFlip {α : Type} [DecidableEq α] (c : α) (m : α → Bool) : α → Bool :=
  Function.update m c (!m c)

private theorem maskFlip_involutive {α : Type} [DecidableEq α] (c : α) : Function.Involutive (maskFlip c) := by
  intro m
  unfold maskFlip
  simp only [Function.update_self, Bool.not_not, Function.update_idem]
  exact Function.update_eq_self c m

private theorem mask_maskFlip_weighted_regroup {α : Type} [Fintype α] [DecidableEq α]
    (a b : ℝ) (p : (α → Bool) → ℝ)
    (balance : ∀ m c, a * p (Function.update m c true) = b * p (Function.update m c false))
    (cost : (α → Bool) → α → ℝ) :
    a * (∑ c : α, ∑ m : α → Bool, if m c then p m * cost (Function.update m c false) c else 0) =
    b * (∑ c : α, ∑ m : α → Bool, if m c then 0 else p m * cost m c) := by
  classical
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum,Finset.mul_sum]
  let e : (α → Bool) ≃ (α → Bool) := Function.Involutive.toPerm (maskFlip c) (maskFlip_involutive c)
  let L : (α → Bool) → ℝ := fun m => a * (if m c then p m * cost (Function.update m c false) c else 0)
  have hre : (∑ m, L m) = ∑ m, L (e m) := (e.sum_comp L).symm
  change (∑ m, L m) = _
  rw [hre]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hm0 : m c = false
  · have hmtrue : maskFlip c m = Function.update m c true := by simp [maskFlip,hm0]
    have hmfalse : Function.update m c false = m := by rw [← hm0]; exact Function.update_eq_self c m
    have hb := balance m c
    rw [hmfalse] at hb
    simp [L,e,hmtrue,hm0,Function.update_idem,hmfalse]
    nlinarith [congrArg (fun x : ℝ => x * cost m c) hb]
  · have hmtrue : m c = true := by cases h : m c <;> simp_all
    simp [L,e,maskFlip,hmtrue]

theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (cost : (α → Bool) → α → ℝ) :
    let P : (α → Bool) → ℝ := fun m => (Measure.pi (fun _ : α => unitPriorityMeasure)
      (Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2)))).toReal
    (ε / 2) * (∑ c : α, ∑ m : α → Bool, if m c then P m * cost (Function.update m c false) c else 0) =
    (1 - ε / 2) * (∑ c : α, ∑ m : α → Bool, if m c then 0 else P m * cost m c) := by
  classical
  apply mask_maskFlip_weighted_regroup
  intro m c
  exact first_mask_single_flip_probability_balance ε hε0 hε1 m c
