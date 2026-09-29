-- Prove2me | solution 1 for TSPHeuristics.KOpt.theorem_5_proof_circle_lengths
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:54:41.297169+00:00
-- url     : https://prove2.me/submissions/3175369a-6ac3-4fcc-9e51-04b2d87c7f1b

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_KOpt_CircleInstance

namespace TSPHeuristics.KOpt

/-- distance on naturals -/
def aux_c5_D (n : ℕ) (a b : ℕ) : ℝ :=
  ((min ((a + n - b) % n) ((b + n - a) % n) : ℕ) : ℝ)

theorem aux_c5_mod (n a b : ℕ) (ha : a < n) (hb : b < n) :
    (a + n - b) % n = if b ≤ a then a - b else a + n - b := by
  split_ifs with h
  · have : a + n - b = (a - b) + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

theorem aux_c5_D_eq (n a b : ℕ) (ha : a < n) (hb : b < n) :
    aux_c5_D n a b = ((min (if b ≤ a then a - b else a + n - b)
      (if a ≤ b then b - a else b + n - a) : ℕ) : ℝ) := by
  unfold aux_c5_D
  rw [aux_c5_mod n a b ha hb, aux_c5_mod n b a hb ha]

/-- chain sum -/
def aux_c5_chain (D : ℕ → ℕ → ℝ) : List ℕ → ℝ
  | x :: y :: rest => D x y + aux_c5_chain D (y :: rest)
  | _ => 0

theorem aux_c5_chain_cons2 (D : ℕ → ℕ → ℝ) (x y : ℕ) (r : List ℕ) :
    aux_c5_chain D (x :: y :: r) = D x y + aux_c5_chain D (y :: r) := rfl

theorem aux_c5_zip (D : ℕ → ℕ → ℝ) (l : List ℕ) :
    ∀ x y : ℕ, (List.zipWith D (x :: l) (l ++ [y])).sum = aux_c5_chain D (x :: l ++ [y]) := by
  induction l with
  | nil => intro x y; simp [aux_c5_chain]
  | cons z l ih =>
    intro x y
    simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
    rw [aux_c5_chain_cons2, ← List.cons_append, ← ih]

theorem aux_c5_chain_append (D : ℕ → ℕ → ℝ) (x y : ℕ) (r : List ℕ) (l : List ℕ) :
    aux_c5_chain D (l ++ x :: y :: r) = aux_c5_chain D (l ++ [x]) + D x y +
      aux_c5_chain D (y :: r) := by
  induction l with
  | nil => simp [aux_c5_chain]
  | cons z l ih =>
    cases l with
    | nil => simp [aux_c5_chain]; ring
    | cons w l =>
      simp only [List.cons_append] at ih ⊢
      rw [aux_c5_chain_cons2, ih, aux_c5_chain_cons2]; ring

theorem aux_c5_odd_chain (D : ℕ → ℕ → ℝ) (m : ℕ)
    (h : ∀ j, j < m → D (2 * j + 1) (2 * (j + 1) + 1) = 2) :
    aux_c5_chain D ((List.range (m + 1)).map (fun j => 2 * j + 1)) = 2 * m := by
  induction m with
  | zero => simp [aux_c5_chain]
  | succ m ih =>
    rw [show (List.range (m + 1 + 1)).map (fun j => 2 * j + 1) =
        (List.range m).map (fun j => 2 * j + 1) ++ (2 * m + 1) :: (2 * (m + 1) + 1) :: [] by
          simp [List.range_succ]]
    rw [aux_c5_chain_append, show (List.range m).map (fun j => 2 * j + 1) ++ [2 * m + 1] =
        (List.range (m + 1)).map (fun j => 2 * j + 1) by simp [List.range_succ],
      ih (fun j hj => h j (by omega)), h m (by omega)]
    simp [aux_c5_chain]; ring

theorem aux_c5_rev_succ (g : ℕ → ℕ) (k : ℕ) :
    ((List.range (k + 1)).map g).reverse = g k :: ((List.range k).map g).reverse := by
  simp [List.range_succ]

theorem aux_c5_even_chain (D : ℕ → ℕ → ℝ) (p : ℕ)
    (h : ∀ k, k < p → D (2 * (k + 1) + 2) (2 * k + 2) = 2) :
    aux_c5_chain D ((List.range (p + 1)).map (fun j => 2 * j + 2)).reverse = 2 * p := by
  induction p with
  | zero => simp [aux_c5_chain]
  | succ p ih =>
    rw [show ((List.range (p + 1 + 1)).map (fun j => 2 * j + 2)).reverse =
        (2 * (p + 1) + 2) :: (2 * p + 2) :: ((List.range p).map (fun j => 2 * j + 2)).reverse by
          simp [List.range_succ]]
    rw [aux_c5_chain_cons2, show (2 * p + 2) :: ((List.range p).map (fun j => 2 * j + 2)).reverse
        = ((List.range (p + 1)).map (fun j => 2 * j + 2)).reverse by simp [List.range_succ],
      ih (fun k hk => h k (by omega)), h p (by omega)]
    push_cast; ring

theorem aux_c5_filter_zero (N : ℕ) (hN : 1 ≤ N) :
    (List.range N).filter (fun k => decide (k = 0)) = [0] := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.filter_append]
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · rw [ih h]; simp; omega

theorem aux_c5_filter_odd (N : ℕ) :
    (List.range N).filter (fun k => decide (k % 2 = 1)) =
      (List.range (N / 2)).map (fun j => 2 * j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, ih]
    by_cases hN : N % 2 = 1
    · have : (N + 1) / 2 = N / 2 + 1 := by omega
      rw [this, List.range_succ, List.map_append]
      simp [hN]; omega
    · have : (N + 1) / 2 = N / 2 := by omega
      rw [this]; simp [hN]

theorem aux_c5_filter_even (N : ℕ) :
    (List.range N).filter (fun k => decide (k ≠ 0 ∧ k % 2 = 0)) =
      (List.range ((N - 1) / 2)).map (fun j => 2 * j + 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, ih]
    by_cases hN : N ≠ 0 ∧ N % 2 = 0
    · have : (N + 1 - 1) / 2 = (N - 1) / 2 + 1 := by omega
      rw [this, List.range_succ, List.map_append]
      simp [hN]; omega
    · have : (N + 1 - 1) / 2 = (N - 1) / 2 := by omega
      rw [this]
      have hN' : ¬ (N ≠ 0 ∧ N % 2 = 0) := hN
      simp only [List.filter_cons, List.filter_nil]
      rw [if_neg (by simpa using hN')]
      simp

theorem aux_c5_vals (n : ℕ) (hn : 1 ≤ n) :
    (circleSubtour n n).map Fin.val = 0 :: ((List.range (n / 2)).map (fun j => 2 * j + 1) ++
      ((List.range ((n - 1) / 2)).map (fun j => 2 * j + 2)).reverse) := by
  unfold circleSubtour
  simp only [List.map_append, List.map_reverse]
  have key : ∀ (P : Fin n → Bool) (Q : ℕ → Bool), (∀ m : Fin n, P m = Q m.val) →
      ((List.finRange n).filter P).map Fin.val = (List.range n).filter Q := by
    intro P Q hPQ
    have : P = Q ∘ Fin.val := funext hPQ
    rw [this, ← List.filter_map, List.map_coe_finRange_eq_range]
  rw [key _ (fun k => decide (k = 0)) (fun m => by simp [m.isLt]),
    key _ (fun k => decide (k % 2 = 1)) (fun m => by simp [m.isLt, Nat.odd_iff]),
    key _ (fun k => decide (k ≠ 0 ∧ k % 2 = 0)) (fun m => by simp [m.isLt, Nat.even_iff]),
    aux_c5_filter_zero n hn, aux_c5_filter_odd, aux_c5_filter_even]
  simp

theorem aux_c5_part1 (n : ℕ) (hn : 6 ≤ n) :
    TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n n) = 2 * ((n : ℝ) - 1) := by
  unfold TSPHeuristics.Shared.cycleLength
  have hcd : cycDist n = fun i j => aux_c5_D n i.val j.val := rfl
  have e1 : List.zipWith (cycDist n) (circleSubtour n n) ((circleSubtour n n).rotate 1) =
      List.zipWith (aux_c5_D n) ((circleSubtour n n).map Fin.val)
        (((circleSubtour n n).map Fin.val).rotate 1) := by
    rw [← List.map_rotate, List.zipWith_map, hcd]
  rw [e1, aux_c5_vals n (by omega), List.rotate_cons_succ, List.rotate_zero, aux_c5_zip]
  -- set up
  obtain ⟨m, hm⟩ : ∃ m, n / 2 = m + 1 := ⟨n / 2 - 1, by omega⟩
  obtain ⟨p, hp⟩ : ∃ p, (n - 1) / 2 = p + 1 := ⟨(n - 1) / 2 - 1, by omega⟩
  rw [hm, hp]
  have hD : ∀ a b, a < n → b < n → aux_c5_D n a b = ((min (if b ≤ a then a - b else a + n - b)
      (if a ≤ b then b - a else b + n - a) : ℕ) : ℝ) := fun a b ha hb => aux_c5_D_eq n a b ha hb
  have hOc := aux_c5_odd_chain (aux_c5_D n) m (fun j hj => by
    rw [hD _ _ (by omega) (by omega)]; norm_cast; split_ifs <;> omega)
  have hEc := aux_c5_even_chain (aux_c5_D n) p (fun k hk => by
    rw [hD _ _ (by omega) (by omega)]; norm_cast; split_ifs <;> omega)
  set O := (List.range (m + 1)).map (fun j => 2 * j + 1) with hO
  set E := ((List.range (p + 1)).map (fun j => 2 * j + 2)).reverse with hE
  have hO1 : ∃ r, O = 1 :: r := ⟨_, by rw [hO, List.range_succ_eq_map]; simp; rfl⟩
  have hO2 : ∃ Oi, O = Oi ++ [2 * m + 1] := ⟨_, by rw [hO, List.range_succ, List.map_append]; rfl⟩
  have hE1 : ∃ Et, E = (2 * p + 2) :: Et := ⟨_, by rw [hE, aux_c5_rev_succ]⟩
  have hE2 : ∃ Et, E = Et ++ [2] := ⟨_, by
    rw [hE, List.range_succ_eq_map, List.map_cons, List.reverse_cons]⟩
  clear_value O E
  obtain ⟨r, hr⟩ := hO1
  obtain ⟨Et2, hEt2⟩ := hE2
  obtain ⟨Oi, rfl⟩ := hO2
  obtain ⟨Et, rfl⟩ := hE1
  have eq1 : 0 :: (Oi ++ [2 * m + 1] ++ (2 * p + 2) :: Et) ++ [0] =
      (0 :: Oi) ++ (2 * m + 1) :: (2 * p + 2) :: (Et ++ [0]) := by simp
  rw [eq1, aux_c5_chain_append]
  have eq2 : aux_c5_chain (aux_c5_D n) (0 :: Oi ++ [2 * m + 1]) =
      aux_c5_D n 0 1 + aux_c5_chain (aux_c5_D n) (Oi ++ [2 * m + 1]) := by
    rw [List.cons_append, hr, aux_c5_chain_cons2]
  have eq3 : aux_c5_chain (aux_c5_D n) ((2 * p + 2) :: (Et ++ [0])) =
      aux_c5_chain (aux_c5_D n) ((2 * p + 2) :: Et) + aux_c5_D n 2 0 := by
    rw [← List.cons_append, hEt2, List.append_assoc, List.singleton_append,
      aux_c5_chain_append]
    simp [aux_c5_chain]
  rw [eq2, eq3, hOc, hEc]
  have d01 : aux_c5_D n 0 1 = 1 := by
    rw [hD _ _ (by omega) (by omega)]; norm_cast; split_ifs <;> omega
  have d20 : aux_c5_D n 2 0 = 2 := by
    rw [hD _ _ (by omega) (by omega)]; norm_cast; split_ifs <;> omega
  have dmid : aux_c5_D n (2 * m + 1) (2 * p + 2) = 1 := by
    rw [hD _ _ (by omega) (by omega)]; norm_cast; split_ifs <;> omega
  rw [d01, d20, dmid]
  have hmp : (m : ℝ) + p + 3 = n := by
    have : m + p + 3 = n := by omega
    exact_mod_cast this
  rw [← hmp]; ring

theorem aux_c5_dist_pos (n : ℕ) (i j : Fin n) (h : i ≠ j) : 1 ≤ cycDist n i j := by
  have hij : i.val ≠ j.val := fun e => h (Fin.ext e)
  have : cycDist n i j = aux_c5_D n i.val j.val := rfl
  rw [this, aux_c5_D_eq n _ _ i.isLt j.isLt]
  have hi := i.isLt; have hj := j.isLt
  norm_cast; split_ifs <;> omega

theorem aux_c5_part2 (n : ℕ) (hn : 6 ≤ n) :
    TSPHeuristics.Shared.optimal (cycDist n) = n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  unfold TSPHeuristics.Shared.optimal
  apply le_antisymm
  · refine le_trans (Finset.inf'_le _ (Finset.mem_univ (1 : Equiv.Perm (Fin (n' + 1))))) ?_
    unfold TSPHeuristics.Shared.tourLength
    have : ∀ k : Fin (n' + 1), cycDist (n' + 1) ((1 : Equiv.Perm (Fin (n' + 1))) k)
        ((1 : Equiv.Perm (Fin (n' + 1))) (finRotate (n' + 1) k)) = 1 := by
      intro k
      have hk := k.isLt
      have e : cycDist (n' + 1) ((1 : Equiv.Perm (Fin (n' + 1))) k)
        ((1 : Equiv.Perm (Fin (n' + 1))) (finRotate (n' + 1) k)) =
          aux_c5_D (n' + 1) k.val (finRotate (n' + 1) k).val := rfl
      have hr := coe_finRotate k
      have hlt := (finRotate (n' + 1) k).isLt
      rw [e, aux_c5_D_eq _ _ _ hk hlt, hr]
      by_cases hl : k = Fin.last n'
      · have : k.val = n' := by rw [hl]; simp
        rw [if_pos hl]; norm_cast; split_ifs <;> omega
      · have : k.val ≠ n' := fun e => hl (Fin.ext (by simp [e]))
        rw [if_neg hl]; norm_cast; split_ifs <;> omega
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  · apply Finset.le_inf'
    intro τ _
    unfold TSPHeuristics.Shared.tourLength
    have : ∀ k : Fin (n' + 1), (1 : ℝ) ≤ cycDist (n' + 1) (τ k) (τ (finRotate (n' + 1) k)) := by
      intro k
      apply aux_c5_dist_pos
      intro e
      have e2 := τ.injective e
      have hr := coe_finRotate k
      have hk := k.isLt
      have := congrArg Fin.val e2
      rw [hr] at this
      split_ifs at this with hl
      · have : k.val = n' := by rw [hl]; simp
        omega
      · omega
    calc ((n' + 1 : ℕ) : ℝ) = ∑ _k : Fin (n' + 1), (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun k _ => this k)

end TSPHeuristics.KOpt

open TSPHeuristics.KOpt

theorem solution (n : ℕ) (hn : 6 ≤ n) :
    TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n n) = 2 * ((n : ℝ) - 1) ∧
      TSPHeuristics.Shared.optimal (cycDist n) = n :=
  ⟨aux_c5_part1 n hn, aux_c5_part2 n hn⟩
