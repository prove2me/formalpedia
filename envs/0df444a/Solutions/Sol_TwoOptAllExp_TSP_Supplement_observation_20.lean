-- Prove2me | solution 1 for TwoOptAllExp.TSP.Supplement.observation_20
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T03:21:49.299337+00:00
-- url     : https://prove2.me/submissions/5866728a-4c2c-4fb7-89a0-4f2cb7beb55a

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA232
namespace TwoOptAllExp.TSP.Supplement.O20

open MCA232 MCA232.Vx

def ex (m s c : ℕ) (x : Vx) : List Vx :=
  match x with
  | v j 1 => if j < m then rho (j + 1) (c + s) ++ [x] else [x]
  | v j 8 => if j < m then x :: alpha (j + 1) else [x]
  | _ => [x]

def ins (m s : ℕ) (P L : List Vx) : List Vx :=
  (List.range L.length).flatMap
    (fun k => ex m s ((P ++ L.take (k + 1)).count (L.getD k (vp 0))) (L.getD k (vp 0)))

lemma ins_nil (m s : ℕ) (P : List Vx) : ins m s P [] = [] := by simp [ins]

lemma ins_append (m s : ℕ) (P L1 L2 : List Vx) :
    ins m s P (L1 ++ L2) = ins m s P L1 ++ ins m s (P ++ L1) L2 := by
  unfold ins
  rw [List.length_append, List.range_add, List.flatMap_append]
  congr 1
  · apply List.flatMap_congr
    intro k hk
    rw [List.mem_range] at hk
    rw [List.getD_append _ _ _ _ hk, List.take_append_of_le_length (by omega)]
  · rw [List.flatMap_map]
    apply List.flatMap_congr
    intro k hk
    rw [List.mem_range] at hk
    have h1 : (L1 ++ L2).getD (L1.length + k) (vp 0) = L2.getD k (vp 0) := by
      rw [List.getD_append_right _ _ _ _ (by omega)]; simp
    rw [h1, show L1.length + k + 1 = L1.length + (k + 1) by omega, List.take_length_add_append,
      List.append_assoc]

lemma ins_single (m s : ℕ) (P : List Vx) (x : Vx) :
    ins m s P [x] = ex m s (P.count x + 1) x := by
  simp [ins, List.count_append]

lemma ins_congr (m m' s s' : ℕ) (P P' L : List Vx)
    (h : ∀ x ∈ L, ∀ c, ex m s (P.count x + c) x = ex m' s' (P'.count x + c) x) :
    ins m s P L = ins m' s' P' L := by
  unfold ins
  apply List.flatMap_congr
  intro k hk
  rw [List.mem_range] at hk
  rw [List.count_append, List.count_append]
  apply h
  rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk

lemma rho_mod (i a b : ℕ) (h : a % 6 = b % 6) : rho i a = rho i b := by
  unfold rho; rw [h]

lemma insertBlocks_eq (m s : ℕ) : insertBlocks m s = ins m s [] (R m) := by
  unfold insertBlocks ins
  apply List.flatMap_congr
  intro k _
  simp only [List.nil_append]
  generalize (R m).getD k (vp 0) = x
  unfold expandAt ex
  rcases x with ⟨j, _ | _ | _ | _ | _ | _ | _ | _ | _ | l⟩ <;> rfl

/-- indices in `R m` are at most `m`. -/
lemma R_idx : ∀ m, ∀ x ∈ R m, ∃ j l, x = v j l ∧ j ≤ m
  | 0, x, hx => by
    simp [R] at hx; rcases hx with rfl | rfl <;> exact ⟨_, _, rfl, le_rfl⟩
  | m + 1, x, hx => by
    simp only [R, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with ((((((((((h | h) | h) | h | h) | h) | h | h) | h) | h | h)))) <;>
      first
      | (subst h; exact ⟨_, _, rfl, le_rfl⟩)
      | (obtain ⟨j, l, rfl, hj⟩ := R_idx m x h; exact ⟨j, l, rfl, by omega⟩)


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


def M : ℕ → List Vx
  | 0 => []
  | m + 1 => [v (m + 1) 2] ++ R m ++ [v (m + 1) 3, v (m + 1) 4] ++ R m ++
      [v (m + 1) 5, v (m + 1) 6] ++ R m ++ [v (m + 1) 7]

lemma R_split : ∀ m, R m = [v m 1] ++ M m ++ [v m 8]
  | 0 => rfl
  | m + 1 => by simp [R, M]

lemma M_idx : ∀ m, ∀ x ∈ M m, ∃ j l, x = v j l ∧ (j < m ∨ (j = m ∧ l ≠ 1 ∧ l ≠ 8))
  | 0, x, hx => by simp [M] at hx
  | m + 1, x, hx => by
    simp only [M, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with (((((((h | h) | h | h) | h) | h | h) | h) | h)) <;>
      first
      | (subst h; exact ⟨_, _, rfl, Or.inr ⟨rfl, by decide, by decide⟩⟩)
      | (obtain ⟨j, l, rfl, hj⟩ := R_idx m x h; exact ⟨j, l, rfl, Or.inl (by omega)⟩)

lemma ex_top (m s c l : ℕ) : ex (m + 1) s c (v (m + 1) l) = [v (m + 1) l] := by
  unfold ex
  rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;> simp

lemma copy (m s s' : ℕ) (P : List Vx) (c0 : ℕ) (hc0 : P.count (v m 1) = c0)
    (h : ∀ j < m, (P.count (v j 1) + s) % 6 = s' % 6) :
    ins (m + 1) s P (R m) = rho (m + 1) (c0 + 1 + s) ++ ins m s' [] (R m) ++ alpha (m + 1) := by
  rw [R_split, ins_append, ins_append, ins_append, ins_append, ins_single, ins_single, ins_single,
    ins_single]
  have hmid : ins (m + 1) s (P ++ [v m 1]) (M m) = ins m s' ([] ++ [v m 1]) (M m) := by
    apply ins_congr
    intro x hx c
    obtain ⟨j, l, rfl, hj⟩ := M_idx m x hx
    rcases hj with hj | ⟨rfl, h1, h8⟩
    · have hjm : j ≠ m := by omega
      unfold ex
      rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;>
        simp [List.count_append, hjm, hj, show j < m + 1 by omega]
      try (apply rho_mod; have := h j hj; omega)
    · unfold ex
      rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;> simp_all
  rw [hmid]
  unfold ex
  simp [hc0, List.count_append] <;> omega

lemma pow3_mod (k : ℕ) : 3 ^ (k + 1) % 6 = 3 := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; omega

lemma cntR (m j : ℕ) (hj : j < m) : (R m).count (v j 1) % 6 = 3 := by
  rw [R_count 1 (Or.inl rfl) m j, if_pos hj.le, show m - j = (m - j - 1) + 1 by omega]
  exact pow3_mod _

theorem main (m s s' : ℕ) (hs : (s + 3) % 6 = s' % 6) (hs' : (s' + 3) % 6 = s % 6) (hs6 : s < 6) :
    ins (m + 1) s [] (R (m + 1)) =
      [v (m + 1) 1, v (m + 1) 2] ++ rho (m + 1) (1 + s) ++ ins m s [] (R m) ++ alpha (m + 1) ++
        [v (m + 1) 3, v (m + 1) 4] ++ rho (m + 1) (2 + s) ++ ins m s' [] (R m) ++ alpha (m + 1) ++
        [v (m + 1) 5, v (m + 1) 6] ++ rho (m + 1) (3 + s) ++ ins m s [] (R m) ++ alpha (m + 1) ++
        [v (m + 1) 7, v (m + 1) 8] := by
  have two : ∀ (P : List Vx) (a b : ℕ), ins (m + 1) s P [v (m + 1) a, v (m + 1) b] =
      [v (m + 1) a, v (m + 1) b] := by
    intro P a b
    rw [show [v (m + 1) a, v (m + 1) b] = [v (m + 1) a] ++ [v (m + 1) b] from rfl, ins_append,
      ins_single, ins_single, ex_top, ex_top]
  have hne : ∀ j a, j ≤ m → (v (m + 1) a = v j 1 ↔ False) := by
    intro j a hj; simp; omega
  simp only [R.eq_2]
  rw [ins_append, ins_append, ins_append, ins_append, ins_append, ins_append, two, two, two, two]
  have hR1 := R_count 1 (Or.inl rfl) m m
  simp only [le_refl, if_true, Nat.sub_self, pow_zero] at hR1
  rw [copy m s s _ 0 (by simp [List.count_cons]) (by intro j hj; simp [List.count_cons, show ¬ (m + 1 = j) by omega]),
    copy m s s' _ 1 (by simp [List.count_append, List.count_cons, hR1])
      (by intro j hj; have := cntR m j hj
          simp [List.count_append, List.count_cons, show ¬ (m + 1 = j) by omega] <;> omega),
    copy m s s _ 2 (by simp [List.count_append, List.count_cons, hR1])
      (by intro j hj; have := cntR m j hj
          simp [List.count_append, List.count_cons, show ¬ (m + 1 = j) by omega] <;> omega)]
  all_goals (try simp only [List.append_assoc])
  all_goals (try norm_num [Nat.add_comm])

end TwoOptAllExp.TSP.Supplement.O20

namespace TwoOptAllExp.TSP.Supplement
open MCA232 MCA232.Vx

theorem observation_20 :
    Omega 0 = R 0 ∧ OmegaBar 0 = R 0 ∧
    ∀ n : ℕ, 1 ≤ n →
      Omega n = [v n 1, v n 2] ++ rho n 1 ++ Omega (n - 1) ++ alpha n ++
        [v n 3, v n 4] ++ rho n 2 ++ OmegaBar (n - 1) ++ alpha n ++
        [v n 5, v n 6] ++ rho n 3 ++ Omega (n - 1) ++ alpha n ++ [v n 7, v n 8] ∧
      OmegaBar n = [v n 1, v n 2] ++ rho n 4 ++ OmegaBar (n - 1) ++ alpha n ++
        [v n 3, v n 4] ++ rho n 5 ++ Omega (n - 1) ++ alpha n ++
        [v n 5, v n 6] ++ rho n 0 ++ OmegaBar (n - 1) ++ alpha n ++ [v n 7, v n 8] := by
  have e0 : ∀ m, Omega m = O20.ins m 0 [] (R m) := fun m => O20.insertBlocks_eq m 0
  have e3 : ∀ m, OmegaBar m = O20.ins m 3 [] (R m) := fun m => O20.insertBlocks_eq m 3
  refine ⟨by rw [e0]; rfl, by rw [e3]; rfl, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  constructor
  · rw [e0 (m + 1), O20.main m 0 3 (by norm_num) (by norm_num) (by norm_num), ← e0 m, ← e3 m]
  · rw [e3 (m + 1), O20.main m 3 0 (by norm_num) (by norm_num) (by norm_num), ← e0 m, ← e3 m,
      O20.rho_mod (m + 1) (3 + 3) 0 (by norm_num)]

end TwoOptAllExp.TSP.Supplement

open TwoOptAllExp.TSP.Supplement MCA232 MCA232.Vx in
theorem solution :
    Omega 0 = R 0 ∧ OmegaBar 0 = R 0 ∧
    ∀ n : ℕ, 1 ≤ n →
      Omega n = [v n 1, v n 2] ++ rho n 1 ++ Omega (n - 1) ++ alpha n ++
        [v n 3, v n 4] ++ rho n 2 ++ OmegaBar (n - 1) ++ alpha n ++
        [v n 5, v n 6] ++ rho n 3 ++ Omega (n - 1) ++ alpha n ++ [v n 7, v n 8] ∧
      OmegaBar n = [v n 1, v n 2] ++ rho n 4 ++ OmegaBar (n - 1) ++ alpha n ++
        [v n 3, v n 4] ++ rho n 5 ++ Omega (n - 1) ++ alpha n ++
        [v n 5, v n 6] ++ rho n 0 ++ OmegaBar (n - 1) ++ alpha n ++ [v n 7, v n 8] :=
  TwoOptAllExp.TSP.Supplement.observation_20
