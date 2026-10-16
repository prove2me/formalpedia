-- Prove2me | solution 1 for SecretaryAdvice.BinaryLimit.thresholds_ordered
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T08:22:47.113592+00:00
-- url     : https://prove2.me/submissions/9e0c0cfe-239a-4f50-8d58-164c413614fa

import Mathlib
import Definitions.Def_SecretaryAdvice_BinaryLimit_Dual

set_option autoImplicit false
open SecretaryAdvice.BinaryLimit

namespace SecretaryResearch

theorem stages_nonneg (n : ℕ) (p pp : ℝ) (k i : ℕ) (s : Bool) :
    0 ≤ greedyStages n p pp k i s := by
  induction k with
  | zero => simp [greedyStages]
  | succ k ih =>
    simp only [greedyStages]
    split
    · exact le_max_left _ _
    · exact ih

theorem stages_ordered (n : ℕ) (p pp : ℝ) (hp : (1/2 : ℝ) ≤ p)
    (hpp : (1/2 : ℝ) ≤ pp) (k i : ℕ) :
    greedyStages n p pp k i false ≤ greedyStages n p pp k i true := by
  induction k with
  | zero => simp [greedyStages]
  | succ k ih =>
    simp only [greedyStages]
    split
    · simp only [Bool.false_eq_true,if_false,if_true]
      apply max_le_max_left
      have hf : 0 ≤ ∑ j ∈ Finset.Ioc i n,
          (greedyStages n p pp k j true + greedyStages n p pp k j false) :=
        Finset.sum_nonneg (fun j _ => add_nonneg (stages_nonneg ..) (stages_nonneg ..))
      have hc : (1-pp)/(i : ℝ) ≤ pp/(i : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg i)
      have hm := mul_le_mul_of_nonneg_right hc hf
      linarith
    · exact ih

end SecretaryResearch

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Dütting, Lattanzi, Paes Leme and Vassilvitskii, arXiv:2011.06726v1, Theorem 20.
theorem solution (n : ℕ) (p pp : ℝ) (_hn : 1 ≤ n)
    (hp0 : (1/2 : ℝ) ≤ p) (_hp1 : p ≤ 1)
    (hpp0 : (1/2 : ℝ) ≤ pp) (_hpp1 : pp ≤ 1) : tY n p pp ≤ tN n p pp := by
  classical
  have hord (i) : w n p pp i false ≤ w n p pp i true :=
    SecretaryResearch.stages_ordered n p pp hp0 hpp0 n i
  unfold tY tN
  by_cases hN : ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i false
  · have hY : ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i true := by
      obtain ⟨i,hi,hin,hp⟩ := hN
      exact ⟨i,hi,hin,hp.trans_le (hord i)⟩
    rw [if_pos hY,if_pos hN]
    obtain ⟨hi,hin,hp⟩ := Nat.sInf_mem hN
    exact Nat.sInf_le ⟨hi,hin,hp.trans_le (hord _)⟩
  · rw [if_neg hN]
    split_ifs with hY
    · obtain ⟨i,hi,hin,hp⟩ := hY
      have hle : sInf {j : ℕ | 1 ≤ j ∧ j ≤ n ∧ 0 < w n p pp j true} ≤ i :=
        Nat.sInf_le ⟨hi,hin,hp⟩
      exact hle.trans (Nat.le_succ_of_le hin)
    · exact le_rfl

#print axioms solution
