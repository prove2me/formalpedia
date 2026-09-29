-- Prove2me | solution 1 for TSPHeuristics.KOpt.theorem_5_insertion_ratio_two_mul_one_sub_inv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:38:07.97479+00:00
-- url     : https://prove2.me/submissions/11c6adc5-0a85-4eee-96a8-f7656980e66d

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion

namespace TSPHeuristics.KOpt

open TSPHeuristics.Shared

theorem aux_t5_insertIdx_eq {α : Type*} (x : α) : ∀ (L : List α) (p : ℕ), p ≤ L.length →
    L.insertIdx p x = L.take p ++ x :: L.drop p
  | L, 0, _ => by simp
  | [], p+1, h => by simp at h
  | a :: L, p+1, h => by
      simp [List.insertIdx_succ_cons, aux_t5_insertIdx_eq x L p (by simpa using h)]

theorem aux_t5_insertIdx_rotate {α : Type*} (x : α) (L : List α) (p : ℕ) (hp : p ≤ L.length) :
    (L.insertIdx p x).rotate p = x :: L.rotate p := by
  rw [aux_t5_insertIdx_eq x L p hp, List.rotate_eq_drop_append_take hp]
  have h := List.rotate_append_length_eq (L.take p) (x :: L.drop p)
  rw [List.length_take, min_eq_left hp] at h
  rw [h]; simp

theorem aux_t5_cyc_rotate {n : ℕ} (d : Fin n → Fin n → ℝ) (L : List (Fin n)) (r : ℕ) :
    cycleLength d (L.rotate r) = cycleLength d L := by
  unfold cycleLength
  have h : (L.rotate r).rotate 1 = (L.rotate 1).rotate r := by
    rw [List.rotate_rotate, List.rotate_rotate, add_comm]
  rw [h, ← List.zipWith_rotate_distrib _ _ _ _ (by simp)]
  exact (List.rotate_perm _ _).sum_eq

theorem aux_t5_zip_last {n : ℕ} (d : Fin n → Fin n → ℝ) :
    ∀ (rest : List (Fin n)) (m y z : Fin n),
    (List.zipWith d (m :: rest) (rest ++ [y])).sum
      = (List.zipWith d (m :: rest) (rest ++ [z])).sum
        - d ((m :: rest).getLast (List.cons_ne_nil _ _)) z
        + d ((m :: rest).getLast (List.cons_ne_nil _ _)) y
  | [], m, y, z => by simp
  | r :: rest, m, y, z => by
      simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
      rw [aux_t5_zip_last d rest r y z]
      simp only [List.getLast_cons_cons]
      ring

theorem aux_t5_cyc_cons {n : ℕ} (d : Fin n → Fin n → ℝ) (x m : Fin n) (rest : List (Fin n)) :
    cycleLength d (x :: m :: rest) = cycleLength d (m :: rest) + d x m
      + d ((m :: rest).getLast (List.cons_ne_nil _ _)) x
      - d ((m :: rest).getLast (List.cons_ne_nil _ _)) m := by
  unfold cycleLength
  simp only [List.rotate_cons_succ, List.rotate_zero, List.cons_append, List.zipWith_cons_cons,
    List.sum_cons]
  rw [aux_t5_zip_last d rest m x m]
  ring

theorem aux_t5_cyc_ins {n : ℕ} (d : Fin n → Fin n → ℝ) (L : List (Fin n)) (hL : 0 < L.length)
    (p : ℕ) (hp : p ≤ L.length) (x : Fin n) :
    cycleLength d (L.insertIdx p x) = cycleLength d L
      + d x (L[p % L.length]'(Nat.mod_lt _ hL))
      + d (L[(L.length - 1 + p) % L.length]'(Nat.mod_lt _ hL)) x
      - d (L[(L.length - 1 + p) % L.length]'(Nat.mod_lt _ hL))
          (L[p % L.length]'(Nat.mod_lt _ hL)) := by
  rw [← aux_t5_cyc_rotate d (L.insertIdx p x) p, aux_t5_insertIdx_rotate x L p hp,
    ← aux_t5_cyc_rotate d L p]
  obtain ⟨m, rest, hmr⟩ : ∃ m rest, L.rotate p = m :: rest := by
    cases h : L.rotate p with
    | nil =>
      have := congrArg List.length h
      rw [List.length_rotate] at this; simp only [List.length_nil] at this; omega
    | cons m rest => exact ⟨m, rest, rfl⟩
  have hlen : (m :: rest).length = L.length := by rw [← hmr, List.length_rotate]
  have hm : m = L[p % L.length]'(Nat.mod_lt _ hL) := by
    have h1 := List.getElem_rotate L p 0 (by simp; omega)
    have h2 : (L.rotate p)[0]'(by simp; omega) = m := by simp [hmr]
    rw [← h2, h1]; simp
  have hlast : (m :: rest).getLast (List.cons_ne_nil _ _)
      = L[(L.length - 1 + p) % L.length]'(Nat.mod_lt _ hL) := by
    rw [List.getLast_eq_getElem]
    have h1 := List.getElem_rotate L p (L.length - 1) (by simp; omega)
    have h2 : (L.rotate p)[L.length - 1]'(by simp; omega)
        = (m :: rest)[(m :: rest).length - 1]'(by simp) := by
      simp only [hmr, hlen]
    rw [← h2, h1]
  rw [hmr, aux_t5_cyc_cons, hlast, ← hm]

/-! ### Arithmetic -/

/-- Cyclic distance on `ℕ` (for arguments `< n`). -/
def aux_t5_D (n a b : ℕ) : ℕ := min (a - b + (b - a)) (n - (a - b + (b - a)))

theorem aux_t5_D_tri (n a b c : ℕ) (ha : a < n) (hb : b < n) (hc : c < n) :
    aux_t5_D n a c ≤ aux_t5_D n a b + aux_t5_D n b c := by
  unfold aux_t5_D; omega

theorem aux_t5_cost (n i u v x : ℕ) (hn : 6 ≤ n) (hu : u < i) (hv : v < i) (hix : i ≤ x)
    (hx : x < n) (huv : u ≤ v + 2) (hvu : v ≤ u + 2) :
    aux_t5_D n u v + 2 ≤ aux_t5_D n u x + aux_t5_D n x v := by
  unfold aux_t5_D; omega

def aux_t5_g (i k : ℕ) : ℕ := if k = 0 then 0 else if k ≤ i / 2 then 2 * k - 1 else 2 * (i - k)

theorem aux_t5_g_adj (i k : ℕ) (hk : k < i) :
    aux_t5_g i k ≤ aux_t5_g i ((k + 1) % i) + 2 ∧ aux_t5_g i ((k + 1) % i) ≤ aux_t5_g i k + 2 := by
  rcases Nat.lt_or_ge (k + 1) i with h | h
  · rw [Nat.mod_eq_of_lt h]; unfold aux_t5_g; split_ifs <;> first | contradiction | omega
  · have : k + 1 = i := by omega
    rw [this, Nat.mod_self]; unfold aux_t5_g; split_ifs <;> first | contradiction | omega

theorem aux_t5_g_lt (i k : ℕ) (hk : k < i) : aux_t5_g i k < i := by
  unfold aux_t5_g; split_ifs <;> omega

theorem aux_t5_g_succ_lt (i k : ℕ) (hk : k ≤ i / 2) : aux_t5_g (i + 1) k = aux_t5_g i k := by
  unfold aux_t5_g; split_ifs <;> first | contradiction | omega

theorem aux_t5_g_succ_eq (i : ℕ) : aux_t5_g (i + 1) (1 + i / 2) = i := by
  unfold aux_t5_g; split_ifs <;> first | contradiction | omega

theorem aux_t5_g_succ_gt (i k : ℕ) (hk : 1 + i / 2 < k) :
    aux_t5_g (i + 1) k = aux_t5_g i (k - 1) := by
  unfold aux_t5_g; split_ifs <;> first | contradiction | omega

theorem aux_t5_g_prev (i : ℕ) (hi : 2 ≤ i) :
    (aux_t5_g i (i / 2) = i - 1 ∧ aux_t5_g i ((1 + i / 2) % i) = i - 2) ∨
    (aux_t5_g i (i / 2) = i - 2 ∧ aux_t5_g i ((1 + i / 2) % i) = i - 1) := by
  rcases Nat.lt_or_ge (1 + i / 2) i with h | h
  · rw [Nat.mod_eq_of_lt h]; unfold aux_t5_g; split_ifs <;> first | contradiction | omega
  · have : 1 + i / 2 = i := by omega
    rw [this, Nat.mod_self]; unfold aux_t5_g; split_ifs <;> first | contradiction | omega

/-- The chosen insertion costs exactly `2`. -/
theorem aux_t5_cost_eq_nat (n i : ℕ) (hn : 6 ≤ n) (hi : 1 ≤ i) (hin : i < n) :
    aux_t5_D n (aux_t5_g i ((i - 1 + (1 + i / 2)) % i)) i
      + aux_t5_D n i (aux_t5_g i ((1 + i / 2) % i))
      = aux_t5_D n (aux_t5_g i ((i - 1 + (1 + i / 2)) % i)) (aux_t5_g i ((1 + i / 2) % i)) + 2 := by
  rcases Nat.lt_or_ge i 2 with h | h
  · obtain rfl : i = 1 := by omega
    simp only [aux_t5_g, aux_t5_D]
    norm_num
    omega
  · have hq : (i - 1 + (1 + i / 2)) % i = i / 2 := by
      have : i - 1 + (1 + i / 2) = i + i / 2 := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hq]
    rcases aux_t5_g_prev i h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> unfold aux_t5_D <;> omega

/-! ### The instance -/

def aux_t5_d (n : ℕ) (i j : Fin n) : ℝ := (aux_t5_D n i.val j.val : ℝ)

def aux_t5_node (n : ℕ) (hn : 0 < n) (v : ℕ) : Fin n := ⟨v % n, Nat.mod_lt _ hn⟩

def aux_t5_T (n : ℕ) (hn : 0 < n) (i : ℕ) : List (Fin n) :=
  (List.range i).map (fun k => aux_t5_node n hn (aux_t5_g i k))

theorem aux_t5_isTSP (n : ℕ) : IsTSPDist (aux_t5_d n) where
  symm i j := by unfold aux_t5_d aux_t5_D; congr 1; omega
  nonneg i j := by unfold aux_t5_d; positivity
  triangle i j k := by
    unfold aux_t5_d
    exact_mod_cast aux_t5_D_tri n _ _ _ i.isLt j.isLt k.isLt
  diag i := by unfold aux_t5_d aux_t5_D; simp

theorem aux_t5_d_ge_one {n : ℕ} (x y : Fin n) (h : x ≠ y) : 1 ≤ aux_t5_d n x y := by
  unfold aux_t5_d aux_t5_D
  have hx := x.isLt
  have hy := y.isLt
  have : x.val ≠ y.val := fun e => h (Fin.ext e)
  exact_mod_cast (show 1 ≤ min (x.val - y.val + (y.val - x.val)) (n - (x.val - y.val + (y.val - x.val))) by omega)

theorem aux_t5_finRotate_val (n : ℕ) (k : Fin n) :
    ((finRotate n k : Fin n) : ℕ) = if k.val + 1 = n then 0 else k.val + 1 := by
  cases n with
  | zero => exact k.elim0
  | succ m =>
    rw [coe_finRotate]
    have : (k = Fin.last m) ↔ (k.val + 1 = m + 1) := by
      rw [Fin.ext_iff, Fin.val_last]; omega
    by_cases h : k = Fin.last m
    · rw [if_pos h, if_pos (this.mp h)]
    · rw [if_neg h, if_neg (fun e => h (this.mpr e))]

theorem aux_t5_optimal (n : ℕ) (hn : 3 ≤ n) : optimal (aux_t5_d n) = n := by
  unfold optimal
  apply le_antisymm
  · refine (Finset.inf'_le _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))).trans (le_of_eq ?_)
    unfold tourLength
    have : ∀ k : Fin n, aux_t5_d n ((1 : Equiv.Perm (Fin n)) k)
        ((1 : Equiv.Perm (Fin n)) (finRotate n k)) = 1 := by
      intro k
      simp only [Equiv.Perm.coe_one, id]
      unfold aux_t5_d aux_t5_D
      rw [aux_t5_finRotate_val]
      have hk := k.isLt
      split_ifs with h
      · exact_mod_cast (show min (k.val - 0 + (0 - k.val)) (n - (k.val - 0 + (0 - k.val))) = 1 by omega)
      · exact_mod_cast (show min (k.val - (k.val + 1) + (k.val + 1 - k.val))
          (n - (k.val - (k.val + 1) + (k.val + 1 - k.val))) = 1 by omega)
    rw [Finset.sum_congr rfl (fun k _ => this k)]
    simp
  · apply Finset.le_inf'
    intro τ _
    unfold tourLength
    have h1 : ∀ k ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ) ≤ aux_t5_d n (τ k) (τ (finRotate n k)) := by
      intro k _
      apply aux_t5_d_ge_one
      intro e
      have e2 := τ.injective e
      have := congrArg Fin.val e2
      rw [aux_t5_finRotate_val] at this
      have hk := k.isLt
      split_ifs at this <;> omega
    have := Finset.card_nsmul_le_sum _ _ _ h1
    simpa using this

theorem aux_t5_T_length (n : ℕ) (hn : 0 < n) (i : ℕ) : (aux_t5_T n hn i).length = i := by
  simp [aux_t5_T]

theorem aux_t5_T_getElem_val (n : ℕ) (hn : 0 < n) (i : ℕ) (hin : i ≤ n) (j : ℕ)
    (hj : j < (aux_t5_T n hn i).length) : ((aux_t5_T n hn i)[j]).val = aux_t5_g i j := by
  have hj' : j < i := by simpa [aux_t5_T_length] using hj
  simp only [aux_t5_T, List.getElem_map, List.getElem_range, aux_t5_node]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (aux_t5_g_lt i j hj') hin)

theorem aux_t5_node_val (n : ℕ) (hn : 0 < n) (v : ℕ) (hv : v < n) :
    (aux_t5_node n hn v).val = v := Nat.mod_eq_of_lt hv

theorem aux_t5_T_succ (n : ℕ) (hn : 0 < n) (i : ℕ) (hi : 1 ≤ i) :
    aux_t5_T n hn (i + 1) = (aux_t5_T n hn i).insertIdx (1 + i / 2) (aux_t5_node n hn i) := by
  have hp : 1 + i / 2 ≤ (aux_t5_T n hn i).length := by rw [aux_t5_T_length]; omega
  apply List.ext_getElem
  · rw [List.length_insertIdx_of_le_length hp, aux_t5_T_length, aux_t5_T_length]
  · intro k h1 h2
    rw [List.getElem_insertIdx]
    have hk : k < i + 1 := by simpa [aux_t5_T_length] using h1
    split_ifs with ha hb
    · simp only [aux_t5_T, List.getElem_map, List.getElem_range]
      rw [aux_t5_g_succ_lt i k (by omega)]
    · subst hb
      simp only [aux_t5_T, List.getElem_map, List.getElem_range]
      rw [aux_t5_g_succ_eq]
    · simp only [aux_t5_T, List.getElem_map, List.getElem_range]
      rw [aux_t5_g_succ_gt i k (by omega)]

theorem aux_t5_T_one (n : ℕ) (hn : 0 < n) : aux_t5_T n hn 1 = [aux_t5_node n hn 0] := by
  simp [aux_t5_T, aux_t5_g]

theorem aux_t5_T_mem (n : ℕ) (hn : 0 < n) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (y : Fin n) :
    y ∈ aux_t5_T n hn i ↔ y.val < i := by
  induction i, hi using Nat.le_induction generalizing y with
  | base =>
    rw [aux_t5_T_one, List.mem_singleton, Fin.ext_iff, aux_t5_node_val n hn 0 hn]
    omega
  | succ i hi ih =>
    rw [aux_t5_T_succ n hn i hi, List.mem_insertIdx (by rw [aux_t5_T_length]; omega),
      ih (by omega), Fin.ext_iff, aux_t5_node_val n hn i (by omega)]
    omega

theorem aux_t5_cost_ge (n : ℕ) (hn6 : 6 ≤ n) (hn : 0 < n) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n)
    (x : Fin n) (hx : i ≤ x.val) (p : ℕ) (hp : p ≤ i) :
    cycleLength (aux_t5_d n) (aux_t5_T n hn i) + 2
      ≤ cycleLength (aux_t5_d n) ((aux_t5_T n hn i).insertIdx p x) := by
  have hL : 0 < (aux_t5_T n hn i).length := by rw [aux_t5_T_length]; omega
  rw [aux_t5_cyc_ins (aux_t5_d n) _ hL p (by rw [aux_t5_T_length]; exact hp) x]
  unfold aux_t5_d
  rw [aux_t5_T_getElem_val n hn i hin, aux_t5_T_getElem_val n hn i hin]
  simp only [aux_t5_T_length]
  set q := (i - 1 + p) % i with hq
  have hqi : q < i := Nat.mod_lt _ (by omega)
  have hnext : (q + 1) % i = p % i := by
    rw [hq, Nat.mod_add_mod]
    have : i - 1 + p + 1 = p + i := by omega
    rw [this, Nat.add_mod_right]
  have hadj := aux_t5_g_adj i q hqi
  rw [hnext] at hadj
  have hc := aux_t5_cost n i (aux_t5_g i q) (aux_t5_g i (p % i)) x.val hn6
    (aux_t5_g_lt i q hqi) (aux_t5_g_lt i _ (Nat.mod_lt _ (by omega))) hx x.isLt hadj.1 hadj.2
  have hc' : (aux_t5_D n (aux_t5_g i q) (aux_t5_g i (p % i)) : ℝ) + 2
      ≤ (aux_t5_D n (aux_t5_g i q) x.val : ℝ) + (aux_t5_D n x.val (aux_t5_g i (p % i)) : ℝ) := by
    exact_mod_cast hc
  linarith

theorem aux_t5_cost_eq (n : ℕ) (hn6 : 6 ≤ n) (hn : 0 < n) (i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    cycleLength (aux_t5_d n) ((aux_t5_T n hn i).insertIdx (1 + i / 2) (aux_t5_node n hn i))
      = cycleLength (aux_t5_d n) (aux_t5_T n hn i) + 2 := by
  have hL : 0 < (aux_t5_T n hn i).length := by rw [aux_t5_T_length]; omega
  rw [aux_t5_cyc_ins (aux_t5_d n) _ hL _ (by rw [aux_t5_T_length]; omega)]
  unfold aux_t5_d
  rw [aux_t5_T_getElem_val n hn i hin.le, aux_t5_T_getElem_val n hn i hin.le,
    aux_t5_node_val n hn i hin]
  simp only [aux_t5_T_length]
  have h := aux_t5_cost_eq_nat n i hn6 hi hin
  have h' : (aux_t5_D n (aux_t5_g i ((i - 1 + (1 + i / 2)) % i)) i : ℝ)
      + (aux_t5_D n i (aux_t5_g i ((1 + i / 2) % i)) : ℝ)
      = (aux_t5_D n (aux_t5_g i ((i - 1 + (1 + i / 2)) % i)) (aux_t5_g i ((1 + i / 2) % i)) : ℝ)
        + 2 := by
    exact_mod_cast h
  linarith

theorem aux_t5_length (n : ℕ) (hn6 : 6 ≤ n) (hn : 0 < n) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    cycleLength (aux_t5_d n) (aux_t5_T n hn i) = 2 * ((i : ℝ) - 1) := by
  induction i, hi using Nat.le_induction with
  | base =>
    rw [aux_t5_T_one]
    simp [cycleLength, aux_t5_d, aux_t5_D]
  | succ i hi ih =>
    rw [aux_t5_T_succ n hn i hi, aux_t5_cost_eq n hn6 hn i hi (by omega), ih (by omega)]
    push_cast; ring

theorem aux_t5_run (n : ℕ) (hn6 : 6 ≤ n) (hn : 0 < n) :
    IsInsertionRun (aux_t5_d n) (aux_t5_T n hn) (aux_t5_node n hn) := by
  refine ⟨aux_t5_T_one n hn, ?_⟩
  intro i hi hin
  refine ⟨?_, 1 + i / 2, by rw [aux_t5_T_length]; omega, aux_t5_T_succ n hn i hi, ?_⟩
  · rw [aux_t5_T_mem n hn i hi hin.le, aux_t5_node_val n hn i hin]
    omega
  · intro p hp
    rw [aux_t5_T_length] at hp
    rw [aux_t5_T_succ n hn i hi, aux_t5_cost_eq n hn6 hn i hi hin]
    exact aux_t5_cost_ge n hn6 hn i hi hin.le _ (by rw [aux_t5_node_val n hn i hin]) p hp

theorem aux_t5_nearest (n : ℕ) (hn6 : 6 ≤ n) (hn : 0 < n) :
    IsNearestRule (aux_t5_d n) (aux_t5_T n hn) (aux_t5_node n hn) := by
  intro i hi hin x hx
  unfold distToTour
  have hmem : aux_t5_node n hn (i - 1) ∈ (aux_t5_T n hn i).toFinset := by
    rw [List.mem_toFinset, aux_t5_T_mem n hn i hi hin.le, aux_t5_node_val n hn _ (by omega)]
    omega
  refine (Finset.inf_le hmem).trans ?_
  have h1 : aux_t5_d n (aux_t5_node n hn (i - 1)) (aux_t5_node n hn i) = 1 := by
    unfold aux_t5_d aux_t5_D
    rw [aux_t5_node_val n hn _ (by omega), aux_t5_node_val n hn _ hin]
    exact_mod_cast (show min (i - 1 - i + (i - (i - 1))) (n - (i - 1 - i + (i - (i - 1)))) = 1 by omega)
  rw [h1]
  apply Finset.le_inf
  intro y hy
  rw [List.mem_toFinset] at hy
  have hne : y ≠ x := fun e => hx (e ▸ hy)
  exact WithTop.coe_le_coe.mpr (aux_t5_d_ge_one y x hne)

theorem aux_t5_cheapest (n : ℕ) (hn6 : 6 ≤ n) (hn : 0 < n) :
    IsCheapestRule (aux_t5_d n) (aux_t5_T n hn) (aux_t5_node n hn) := by
  intro i hi hin x hx
  unfold insCost
  apply sub_le_sub_right
  have hxi : i ≤ x.val := by
    by_contra h
    exact hx ((aux_t5_T_mem n hn i hi hin.le x).mpr (by omega))
  refine (Finset.inf'_le _ (Finset.mem_range.mpr (show 1 + i / 2 < (aux_t5_T n hn i).length + 1 by
    rw [aux_t5_T_length]; omega))).trans ?_
  rw [aux_t5_cost_eq n hn6 hn i hi hin]
  apply Finset.le_inf'
  intro p hp
  rw [Finset.mem_range, aux_t5_T_length] at hp
  exact aux_t5_cost_ge n hn6 hn i hi hin.le x hxi p (by omega)

end TSPHeuristics.KOpt

open TSPHeuristics.KOpt

theorem solution (n : ℕ) (hn : 6 ≤ n) :
    ∃ d : Fin n → Fin n → ℝ, TSPHeuristics.Shared.IsTSPDist d ∧ 0 < TSPHeuristics.Shared.optimal d ∧
      (∃ (T : ℕ → List (Fin n)) (a : ℕ → Fin n), TSPHeuristics.Shared.IsInsertionRun d T a ∧ TSPHeuristics.Shared.IsNearestRule d T a ∧
        TSPHeuristics.Shared.cycleLength d (T n) = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d) ∧
      (∃ (T : ℕ → List (Fin n)) (a : ℕ → Fin n), TSPHeuristics.Shared.IsInsertionRun d T a ∧ TSPHeuristics.Shared.IsCheapestRule d T a ∧
        TSPHeuristics.Shared.cycleLength d (T n) = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d) := by
  have hn0 : 0 < n := by omega
  have hopt := aux_t5_optimal n (by omega)
  have hlen := aux_t5_length n hn hn0 n (by omega) le_rfl
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have heq : TSPHeuristics.Shared.cycleLength (aux_t5_d n) (aux_t5_T n hn0 n)
      = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal (aux_t5_d n) := by
    rw [hlen, hopt]; field_simp
  refine ⟨aux_t5_d n, aux_t5_isTSP n, ?_, ⟨aux_t5_T n hn0, aux_t5_node n hn0,
    aux_t5_run n hn hn0, aux_t5_nearest n hn hn0, heq⟩,
    ⟨aux_t5_T n hn0, aux_t5_node n hn0, aux_t5_run n hn hn0, aux_t5_cheapest n hn hn0, heq⟩⟩
  rw [hopt]; exact_mod_cast hn0
