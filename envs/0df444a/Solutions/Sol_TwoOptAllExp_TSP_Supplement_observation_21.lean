-- Prove2me | solution 1 for TwoOptAllExp.TSP.Supplement.observation_21
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T03:11:19.802198+00:00
-- url     : https://prove2.me/submissions/6dc83b84-d8ef-4f92-ba67-95a2db57e854

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA232
namespace TwoOptAllExp.TSP.Supplement.O21

open MCA232 MCA232.Vx

lemma rho_len (i k : ℕ) : (rho i k).length = if k % 3 = 0 then 2 else 5 := by
  have h1 : k % 3 = (k % 6) % 3 := by omega
  have h2 : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
  unfold rho
  rw [h1]
  generalize k % 6 = r at h2 ⊢
  interval_cases r <;> simp

lemma expand_len (m s k : ℕ) (x : Vx) :
    (expandAt m s k x).length =
      1 + (match x with
        | v j 1 => if j < m then (if ((((R m).take (k + 1)).count x + s) % 3 = 0) then 2 else 5) else 0
        | v j 8 => if j < m then 5 else 0
        | _ => 0) := by
  unfold expandAt
  rcases x with ⟨j, _ | _ | _ | _ | _ | _ | _ | _ | _ | l⟩ <;> simp <;> split_ifs <;> simp_all [rho_len, alpha]

lemma len_bar (m : ℕ) : (insertBlocks m 3).length = (insertBlocks m 0).length := by
  unfold insertBlocks
  simp only [List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro k _
  rw [expand_len, expand_len]
  generalize (R m).getD k (vp 0) = x
  rcases x with ⟨j, _ | _ | _ | _ | _ | _ | _ | _ | _ | l⟩ <;> simp <;> split_ifs <;> omega

/-- reindexing -/
lemma reindex {α : Type*} [DecidableEq α] (x d : α) (g : ℕ → ℕ) (L : List α) :
    ∑ k ∈ Finset.range L.length, (if L.getD k d = x then g ((L.take (k + 1)).count x) else 0)
      = ∑ c ∈ Finset.range (L.count x), g (c + 1) := by
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton L a ih =>
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
    have hk : ∀ k ∈ Finset.range L.length,
        (if (L ++ [a]).getD k d = x then g (((L ++ [a]).take (k + 1)).count x) else 0) =
        (if L.getD k d = x then g ((L.take (k + 1)).count x) else 0) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [List.getD_append _ _ _ _ hk, List.take_append_of_le_length (by omega)]
    rw [Finset.sum_congr rfl hk, ih, List.count_append]
    simp only [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
      List.take_of_length_le (by simp : (L ++ [a]).length ≤ L.length + 1), List.count_append]
    by_cases h : a = x
    · subst h; simp [Finset.sum_range_succ]
    · simp [h, List.count_singleton]

lemma R_len : ∀ m, (R m).length + 4 = 6 * 3 ^ m
  | 0 => by simp [R]
  | m + 1 => by
    have := R_len m
    simp [R]; rw [pow_succ]; omega

lemma R_count (l : ℕ) (hl : l = 1 ∨ l = 8) :
    ∀ m j, (R m).count (v j l) = if j ≤ m then 3 ^ (m - j) else 0
  | 0, j => by
    rcases hl with rfl | rfl <;> by_cases hj : j = 0 <;> simp_all [R, List.count_cons] <;> omega
  | m + 1, j => by
    have ih := R_count l hl m j
    simp only [R, List.count_append, ih]
    rcases hl with rfl | rfl <;>
    · rcases lt_trichotomy j (m + 1) with h | h | h
      · have h1 : j ≤ m := by omega
        have h2 : m + 1 - j = (m - j) + 1 := by omega
        simp [List.count_cons, h1, h2, pow_succ, show j ≤ m + 1 by omega, show ¬ (1 + m = j) by omega]
        rw [if_neg (by omega)]; ring
      · subst h; simp [List.count_cons]
      · simp [List.count_cons, show ¬ j ≤ m by omega, show ¬ j ≤ m + 1 by omega,
          show ¬ (1 + m = j) by omega, show ¬ (m + 1 = j) by omega]

def f (c : ℕ) : ℕ := if c % 3 = 0 then 2 else 5

lemma f_sum (N : ℕ) : ∑ c ∈ Finset.range (3 * N), f (c + 1) = 12 * N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    have a1 : (3 * N + 1) % 3 = 1 := by omega
    have a2 : (3 * N + 1 + 1) % 3 = 2 := by omega
    have a3 : (3 * N + 1 + 1 + 1) % 3 = 0 := by omega
    simp [f, a1, a2, a3]; ring

lemma S_sum (m : ℕ) : 2 * ∑ j ∈ Finset.range m, 3 ^ (m - j) + 3 = 3 ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have : ∑ j ∈ Finset.range m, 3 ^ (m + 1 - j) = 3 * ∑ j ∈ Finset.range m, 3 ^ (m - j) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj
      rw [Finset.mem_range] at hj
      rw [show m + 1 - j = (m - j) + 1 by omega, pow_succ]; ring
    rw [this, show m + 1 - m = 1 by omega, pow_succ (3:ℕ) (m+1)]
    simp; omega

lemma len_sum (m s : ℕ) : (insertBlocks m s).length =
    ∑ k ∈ Finset.range (R m).length, (expandAt m s k ((R m).getD k (vp 0))).length := by
  unfold insertBlocks
  rw [List.length_flatMap]
  rw [Finset.sum, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]

lemma exp_len0 (m k : ℕ) (x : Vx) : (expandAt m 0 k x).length = 1 + ∑ j ∈ Finset.range m,
    ((if x = v j 1 then f (((R m).take (k + 1)).count (v j 1)) else 0) + (if x = v j 8 then 5 else 0)) := by
  rw [expand_len]
  rcases x with ⟨j, _ | _ | _ | _ | _ | _ | _ | _ | _ | l⟩ <;> simp [Finset.sum_add_distrib, f]

theorem T_eq (m : ℕ) : 2 * T m + 35 = 39 * 3 ^ m := by
  have hT : T m = (R m).length + ∑ j ∈ Finset.range m, 9 * 3 ^ (m - j) := by
    unfold T Omega
    rw [len_sum]
    simp only [exp_len0, Finset.sum_add_distrib]
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, Finset.sum_comm]
    congr 1
    rw [Finset.sum_comm (s := Finset.range (R m).length) (t := Finset.range m), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [reindex (v j 1) (vp 0) f (R m),
      reindex (v j 8) (vp 0) (fun _ => 5) (R m), R_count 1 (Or.inl rfl) m j,
      R_count 8 (Or.inr rfl) m j, if_pos hj.le]
    rw [show m - j = (m - j - 1) + 1 by omega, pow_succ, mul_comm _ 3, f_sum]
    simp; ring
  have h1 := R_len m
  have h2 := S_sum m
  rw [hT, ← Finset.mul_sum, pow_succ] at *
  omega

end TwoOptAllExp.TSP.Supplement.O21

namespace TwoOptAllExp.TSP.Supplement
open MCA232 MCA232.Vx

theorem observation_21 (n : ℕ) :
    (OmegaBar n).length = T n ∧ (T n : ℚ) = (39 * 3 ^ n - 35) / 2 := by
  refine ⟨O21.len_bar n, ?_⟩
  have h := O21.T_eq n
  have h' : ((2 * T n + 35 : ℕ) : ℚ) = ((39 * 3 ^ n : ℕ) : ℚ) := by rw [h]
  push_cast at h'
  linarith

end TwoOptAllExp.TSP.Supplement

open TwoOptAllExp.TSP.Supplement MCA232 in
theorem solution (n : ℕ) :
    (OmegaBar n).length = T n ∧ (T n : ℚ) = (39 * 3 ^ n - 35) / 2 :=
  TwoOptAllExp.TSP.Supplement.observation_21 n
