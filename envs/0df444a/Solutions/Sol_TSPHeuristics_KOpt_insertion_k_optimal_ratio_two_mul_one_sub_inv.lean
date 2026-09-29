-- Prove2me | solution 1 for TSPHeuristics.KOpt.insertion_k_optimal_ratio_two_mul_one_sub_inv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:35:48.722985+00:00
-- url     : https://prove2.me/submissions/4bc8ee4b-35a2-46d5-9da6-c0032768e3b6

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion
import Definitions.Def_TSPHeuristics_KOpt_KOptimal

open Classical

namespace TSPHeuristics.KOpt

open TSPHeuristics.Shared Fin.NatCast

def PS {n : ℕ} (d : Fin n → Fin n → ℝ) (x : Fin n) (L : List (Fin n)) (y : Fin n) : ℝ :=
  (List.zipWith d (x :: L) (L ++ [y])).sum

lemma PS_nil {n : ℕ} (d : Fin n → Fin n → ℝ) (x y : Fin n) : PS d x [] y = d x y := by
  simp [PS]

lemma PS_cons {n : ℕ} (d : Fin n → Fin n → ℝ) (x h y : Fin n) (L : List (Fin n)) :
    PS d x (h :: L) y = d x h + PS d h L y := by
  simp [PS]

lemma PS_append {n : ℕ} (d : Fin n → Fin n → ℝ) (L1 : List (Fin n)) :
    ∀ (x z y : Fin n) (L2 : List (Fin n)), PS d x (L1 ++ z :: L2) y = PS d x L1 z + PS d z L2 y := by
  induction L1 with
  | nil => intro x z y L2; simp [PS_cons, PS_nil]
  | cons h L ih => intro x z y L2; rw [List.cons_append, PS_cons, PS_cons, ih]; ring

lemma cycle_cons {n : ℕ} (d : Fin n → Fin n → ℝ) (x : Fin n) (L : List (Fin n)) :
    cycleLength d (x :: L) = PS d x L x := by
  simp [cycleLength, PS]

lemma cycle_swap {n : ℕ} (d : Fin n → Fin n → ℝ) (A B : List (Fin n)) :
    cycleLength d (A ++ B) = cycleLength d (B ++ A) := by
  rcases A with _ | ⟨x, A'⟩
  · simp
  rcases B with _ | ⟨z, B'⟩
  · simp
  rw [List.cons_append, List.cons_append, cycle_cons, cycle_cons, PS_append, PS_append]
  ring

lemma cycle_ins_gen {n : ℕ} (d : Fin n → Fin n → ℝ) (x : Fin n) (C : List (Fin n)) (hC : C ≠ []) :
    cycleLength d (x :: C) = cycleLength d C + d x (C.head hC) + d (C.getLast hC) x
      - d (C.getLast hC) (C.head hC) := by
  obtain ⟨D, ℓ, rfl⟩ : ∃ D ℓ, C = D ++ [ℓ] :=
    ⟨C.dropLast, C.getLast hC, (List.dropLast_append_getLast hC).symm⟩
  rcases D with _ | ⟨c, D'⟩
  · simp [cycle_cons, PS_cons, PS_nil]; ring
  · simp only [List.cons_append, cycle_cons, PS_cons, List.head_cons]
    rw [PS_append, PS_append, PS_nil, PS_nil]
    simp
    ring

lemma insertIdx_app {α : Type*} (A B : List α) (x : α) :
    (A ++ B).insertIdx A.length x = A ++ x :: B := by
  induction A with
  | nil => simp
  | cons a A ih => simp [List.insertIdx_succ_cons, ih]

lemma cycle_mid {n : ℕ} (d : Fin n → Fin n → ℝ) (x : Fin n) (A B : List (Fin n))
    (hA : A ≠ []) (hB : B ≠ []) :
    cycleLength d (A ++ x :: B) = cycleLength d (A ++ B) + d (A.getLast hA) x + d x (B.head hB)
      - d (A.getLast hA) (B.head hB) := by
  have e1 : cycleLength d (A ++ x :: B) = cycleLength d (x :: (B ++ A)) := by rw [cycle_swap]; rfl
  have e2 : cycleLength d (A ++ B) = cycleLength d (B ++ A) := cycle_swap d A B
  rw [e1, e2, cycle_ins_gen d x (B ++ A) (by simp [hB])]
  rw [List.head_append_of_ne_nil hB, List.getLast_append_of_ne_nil _ hA]
  ring

lemma ins_lb {n : ℕ} (d : Fin n → Fin n → ℝ) (L : List (Fin n)) (hL : L ≠ []) (x : Fin n) (c : ℝ)
    (H1 : ∀ p (h : p + 1 < L.length), c ≤ d L[p] x + d x L[p+1] - d L[p] L[p+1])
    (H2 : c ≤ d (L.getLast hL) x + d x (L.head hL) - d (L.getLast hL) (L.head hL)) :
    ∀ p ≤ L.length, cycleLength d L + c ≤ cycleLength d (L.insertIdx p x) := by
  intro p hp
  have e := insertIdx_app (L.take p) (L.drop p) x
  rw [List.take_append_drop, List.length_take, min_eq_left hp] at e
  rw [e]
  rcases Nat.eq_zero_or_pos p with h0 | hpos
  · subst h0
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    rw [cycle_ins_gen d x L hL]; linarith
  rcases Nat.lt_or_ge p L.length with hlt | hge
  · have hA : L.take p ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
    have hB : L.drop p ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
    rw [cycle_mid d x _ _ hA hB, List.take_append_drop]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have h1 := H1 q hlt
    rw [List.getLast_eq_getElem, List.head_drop]
    simp only [List.getElem_take, List.length_take]
    have : min (q + 1) L.length - 1 = q := by omega
    simp only [this]
    linarith
  · have hp' : p = L.length := by omega
    subst hp'
    simp only [List.take_length, List.drop_length]
    rw [cycle_swap, List.singleton_append, cycle_ins_gen d x L hL]; linarith

/-! distance -/

def ad (a b : ℕ) : ℕ := if a ≤ b then b - a else a - b
def dN (n a b : ℕ) : ℕ := min (ad a b) (n - ad a b)

noncomputable def dd (n : ℕ) : Fin n → Fin n → ℝ := fun i j => ((dN n i.val j.val : ℕ) : ℝ)

lemma dd_tsp (n : ℕ) : IsTSPDist (dd n) where
  symm := by intro i j; simp only [dd]; congr 1; unfold dN ad; split_ifs <;> omega
  nonneg := by intro i j; simp [dd]
  triangle := by
    intro i j k; simp only [dd]; rw [← Nat.cast_add, Nat.cast_le]
    have := i.isLt; have := j.isLt; have := k.isLt
    unfold dN ad; split_ifs <;> omega
  diag := by intro i; simp [dd, dN, ad]

lemma finval_add_one {N : ℕ} (i : Fin (N+1)) : (i+1).val = if i.val = N then 0 else i.val + 1 := by
  rw [Fin.val_add_one]
  by_cases h : i = Fin.last N
  · subst h; simp
  · rw [if_neg h, if_neg]; intro h'; exact h (Fin.ext (by simpa using h'))

lemma rot_val {N : ℕ} (i : Fin (N+1)) :
    (finRotate (N+1) i).val = if i.val = N then 0 else i.val + 1 := by
  rw [finRotate_succ_apply, finval_add_one]

lemma optimal_dd (N : ℕ) (hN : 2 ≤ N) : optimal (dd (N+1)) = (N + 1 : ℕ) := by
  apply le_antisymm
  · have : tourLength (dd (N+1)) (Equiv.refl _) = (N+1 : ℕ) := by
      unfold tourLength
      have : ∀ k : Fin (N+1), dd (N+1) ((Equiv.refl (Fin (N+1))) k) ((Equiv.refl (Fin (N+1))) (finRotate (N+1) k)) = 1 := by
        intro k
        simp only [Equiv.refl_apply, dd, rot_val]
        have := k.isLt
        rw [Nat.cast_eq_one]; unfold dN ad; split_ifs <;> omega
      rw [Finset.sum_congr rfl (fun k _ => this k)]; simp
    rw [← this]; exact Finset.inf'_le _ (Finset.mem_univ _)
  · apply Finset.le_inf'
    intro τ _
    unfold tourLength
    have : ∀ k : Fin (N+1), (1:ℝ) ≤ dd (N+1) (τ k) (τ (finRotate (N+1) k)) := by
      intro k
      have hne : τ k ≠ τ (finRotate (N+1) k) := by
        intro h; have := τ.injective h
        have h2 := congrArg Fin.val this; rw [rot_val] at h2; split_ifs at h2 <;> omega
      have hv : (τ k).val ≠ (τ (finRotate (N+1) k)).val := fun h => hne (Fin.ext h)
      have := (τ k).isLt; have := (τ (finRotate (N+1) k)).isLt
      simp only [dd]; rw [Nat.one_le_cast]; unfold dN ad; split_ifs <;> omega
    calc ((N+1 : ℕ) : ℝ) = ∑ _k : Fin (N+1), (1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun k _ => this k)

/-! ## part B : the zigzag run -/

lemma ins_eq_mid {n : ℕ} (d : Fin n → Fin n → ℝ) (L : List (Fin n)) (x : Fin n) (q : ℕ)
    (hq : q + 1 < L.length) :
    cycleLength d (L.insertIdx (q+1) x) = cycleLength d L + d L[q] x + d x L[q+1] - d L[q] L[q+1] := by
  have e := insertIdx_app (L.take (q+1)) (L.drop (q+1)) x
  rw [List.take_append_drop, List.length_take, min_eq_left (by omega)] at e
  rw [e]
  have hA : L.take (q+1) ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
  have hB : L.drop (q+1) ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
  rw [cycle_mid d x _ _ hA hB, List.take_append_drop]
  rw [List.getLast_eq_getElem, List.head_drop]
  simp only [List.getElem_take, List.length_take]
  have : min (q + 1) L.length - 1 = q := by omega
  simp only [this]

def zz (m p : ℕ) : ℕ := if p < (m+1)/2 then 2*p else 2*(m-1-p)+1

def Ev (N m : ℕ) : List (Fin (N+1)) := (List.range ((m+1)/2)).map (fun i => ((2*i : ℕ) : Fin (N+1)))
def Od (N m : ℕ) : List (Fin (N+1)) :=
  ((List.range (m/2)).reverse).map (fun i => ((2*i+1 : ℕ) : Fin (N+1)))
def Z (N m : ℕ) : List (Fin (N+1)) := Ev N m ++ Od N m

lemma Z_length (N m : ℕ) : (Z N m).length = m := by
  simp [Z, Ev, Od]; omega

lemma Z_val (N m : ℕ) (hm : m ≤ N + 1) (p : ℕ) (hp : p < (Z N m).length) :
    ((Z N m)[p]).val = zz m p := by
  have hp' : p < m := by rw [Z_length] at hp; exact hp
  rw [List.getElem_of_eq (show Z N m = Ev N m ++ Od N m from rfl), List.getElem_append]
  split_ifs with h
  · simp only [Ev, List.getElem_map, List.getElem_range, Fin.val_natCast]
    simp [Ev] at h
    rw [Nat.mod_eq_of_lt (by omega)]; unfold zz; rw [if_pos h]
  · simp only [Od, List.getElem_map, List.getElem_reverse, List.getElem_range, Fin.val_natCast,
      List.length_range, List.length_reverse]
    simp [Ev] at h
    simp only [Ev, List.length_map, List.length_range]
    rw [Nat.mod_eq_of_lt (by omega)]; unfold zz; rw [if_neg (by omega)]; omega

lemma Z_val' (N m : ℕ) (hm : m ≤ N + 1) (p : ℕ) (hp : p < m) :
    ((Z N m)[p]'(by rw [Z_length]; exact hp)).val = zz m p := Z_val N m hm p _

lemma natCast_val (N m : ℕ) (hm : m < N + 1) : ((m : ℕ) : Fin (N+1)).val = m := by
  rw [Fin.val_natCast, Nat.mod_eq_of_lt hm]

lemma Z_mem (N m : ℕ) (hm : m ≤ N + 1) (x : Fin (N+1)) : x ∈ Z N m ↔ x.val < m := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Z_val N m hm p hp]; rw [Z_length] at hp; unfold zz; split_ifs <;> omega
  · intro hx
    by_cases he : x.val % 2 = 0
    · refine ⟨x.val / 2, by rw [Z_length]; omega, Fin.ext ?_⟩
      rw [Z_val N m hm]; unfold zz; rw [if_pos (by omega)]; omega
    · refine ⟨m - 1 - x.val / 2, by rw [Z_length]; omega, Fin.ext ?_⟩
      rw [Z_val N m hm]; unfold zz; rw [if_neg (by omega)]; omega

lemma Z_step (N m : ℕ) (hm : m + 1 ≤ N + 1) :
    Z N (m+1) = (Z N m).insertIdx ((m+1)/2) ((m : ℕ) : Fin (N+1)) := by
  apply List.ext_getElem
  · rw [List.length_insertIdx_of_le_length (by rw [Z_length]; omega), Z_length, Z_length]
  · intro j h1 h2
    rw [List.getElem_insertIdx]
    apply Fin.ext
    rw [Z_val N (m+1) hm]
    have hj : j < m + 1 := by rw [Z_length] at h1; exact h1
    split_ifs with ha hb
    · rw [Z_val N m (by omega)]; unfold zz; split_ifs <;> omega
    · rw [natCast_val N m (by omega)]; unfold zz; split_ifs <;> omega
    · rw [Z_val N m (by omega)]; unfold zz; split_ifs <;> omega

lemma Z_one (N : ℕ) : Z N 1 = [((0 : ℕ) : Fin (N+1))] := by
  simp [Z, Ev, Od]

lemma dd_val {N : ℕ} (i j : Fin (N+1)) : dd (N+1) i j = ((dN (N+1) i.val j.val : ℕ) : ℝ) := rfl

lemma key_real (N m : ℕ) (hN : 5 ≤ N) (i j x : Fin (N+1)) (hi : i.val < m) (hj : j.val < m)
    (hx : m ≤ x.val) (hij : ad i.val j.val ≤ 2) :
    (2:ℝ) ≤ dd (N+1) i x + dd (N+1) x j - dd (N+1) i j := by
  rw [dd_val, dd_val, dd_val]
  have hxn := x.isLt
  have : dN (N+1) i.val j.val + 2 ≤ dN (N+1) i.val x.val + dN (N+1) x.val j.val := by
    unfold dN ad at *; split_ifs at * <;> omega
  have h2 : ((dN (N+1) i.val j.val : ℕ) : ℝ) + 2 ≤ (dN (N+1) i.val x.val : ℕ) + (dN (N+1) x.val j.val : ℕ) := by
    exact_mod_cast this
  linarith

lemma Z_ne_nil (N m : ℕ) (hm : 1 ≤ m) : Z N m ≠ [] :=
  List.ne_nil_of_length_pos (by rw [Z_length]; omega)

lemma Z_lb (N m : ℕ) (hN : 5 ≤ N) (hm1 : 1 ≤ m) (hm : m ≤ N + 1) (x : Fin (N+1)) (hx : m ≤ x.val) :
    ∀ p ≤ (Z N m).length, cycleLength (dd (N+1)) (Z N m) + 2 ≤
      cycleLength (dd (N+1)) ((Z N m).insertIdx p x) := by
  apply ins_lb _ _ (Z_ne_nil N m hm1)
  · intro p hp
    have hp' : p + 1 < m := by rw [Z_length] at hp; exact hp
    apply key_real N m hN _ _ x
    · rw [Z_val N m hm]; unfold zz; split_ifs <;> omega
    · rw [Z_val N m hm]; unfold zz; split_ifs <;> omega
    · exact hx
    · rw [Z_val N m hm, Z_val N m hm]; unfold zz ad; split_ifs <;> omega
  · rw [List.getLast_eq_getElem, List.head_eq_getElem]
    have hl : (Z N m).length - 1 = m - 1 := by rw [Z_length]
    apply key_real N m hN _ _ x
    · rw [Z_val N m hm]; simp only [Z_length]; unfold zz; split_ifs <;> omega
    · rw [Z_val N m hm]; unfold zz; split_ifs <;> omega
    · exact hx
    · rw [Z_val N m hm, Z_val N m hm]; simp only [Z_length]; unfold zz ad; split_ifs <;> omega

lemma Z_cycle_step (N m : ℕ) (hN : 5 ≤ N) (hm1 : 1 ≤ m) (hm : m + 1 ≤ N + 1) :
    cycleLength (dd (N+1)) (Z N (m+1)) = cycleLength (dd (N+1)) (Z N m) + 2 := by
  rw [Z_step N m hm]
  rcases Nat.lt_or_ge 1 m with h2 | h1
  · obtain ⟨q, hq⟩ : ∃ q, (m+1)/2 = q + 1 := ⟨(m+1)/2 - 1, by omega⟩
    rw [hq, ins_eq_mid _ _ _ q (by rw [Z_length]; omega)]
    rw [dd_val, dd_val, dd_val, Z_val N m (by omega), Z_val N m (by omega),
      natCast_val N m (by omega)]
    have : dN (N+1) (zz m q) m + dN (N+1) m (zz m (q+1)) = dN (N+1) (zz m q) (zz m (q+1)) + 2 := by
      unfold dN ad zz; split_ifs <;> omega
    have h2 : ((dN (N+1) (zz m q) m : ℕ) : ℝ) + (dN (N+1) m (zz m (q+1)) : ℕ) =
        (dN (N+1) (zz m q) (zz m (q+1)) : ℕ) + 2 := by exact_mod_cast this
    linarith
  · have hm' : m = 1 := by omega
    subst hm'
    rw [Z_one]
    have h1 : 1 % (N+1) = 1 := Nat.mod_eq_of_lt (by omega)
    have hN0 : N ≠ 0 := by omega
    simp [cycleLength, dd, dN, ad, h1, hN0]
    have : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    rw [min_eq_left this]; norm_num

lemma Z_cycle (N m : ℕ) (hN : 5 ≤ N) (hm1 : 1 ≤ m) (hm : m ≤ N + 1) :
    cycleLength (dd (N+1)) (Z N m) = 2 * ((m:ℝ) - 1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; rw [Z_one]; simp [cycleLength, dd, dN, ad]
    · rw [Z_cycle_step N m hN hpos hm, ih hpos (by omega)]; push_cast; ring

/-! ## part C : run properties -/

lemma run_ok (N : ℕ) (hN : 5 ≤ N) :
    IsInsertionRun (dd (N+1)) (fun m => Z N m) (fun i => ((i : ℕ) : Fin (N+1))) := by
  refine ⟨Z_one N, ?_⟩
  intro i hi1 hi2
  refine ⟨?_, (i+1)/2, by rw [Z_length]; omega, Z_step N i (by omega), ?_⟩
  · rw [Z_mem N i (by omega), natCast_val N i hi2]; omega
  · intro pos hpos
    rw [Z_cycle_step N i hN hi1 (by omega)]
    exact Z_lb N i hN hi1 (by omega) _ (by rw [natCast_val N i hi2]) pos hpos

lemma dd_ge_one (N : ℕ) (x y : Fin (N+1)) (h : x.val ≠ y.val) : (1:ℝ) ≤ dd (N+1) x y := by
  rw [dd_val]; have := x.isLt; have := y.isLt
  rw [Nat.one_le_cast]; unfold dN ad; split_ifs <;> omega

lemma nearest_ok (N : ℕ) (hN : 5 ≤ N) :
    IsNearestRule (dd (N+1)) (fun m => Z N m) (fun i => ((i : ℕ) : Fin (N+1))) := by
  intro i hi1 hi2 x hx
  simp only at hx ⊢
  have hxv : i ≤ x.val := by rw [Z_mem N i (by omega)] at hx; omega
  unfold distToTour
  have hmem : (((i - 1 : ℕ)) : Fin (N+1)) ∈ (Z N i).toFinset := by
    rw [List.mem_toFinset, Z_mem N i (by omega), natCast_val N _ (by omega)]; omega
  have h1 : (Z N i).toFinset.inf (fun y => ((dd (N+1) y ((i : ℕ) : Fin (N+1)) : ℝ) : WithTop ℝ))
      ≤ ((1 : ℝ) : WithTop ℝ) := by
    refine le_trans (Finset.inf_le hmem) ?_
    rw [WithTop.coe_le_coe, dd_val, natCast_val N _ (by omega), natCast_val N _ (by omega)]
    rw [Nat.cast_le_one]; unfold dN ad; split_ifs <;> omega
  refine le_trans h1 (Finset.le_inf ?_)
  intro y hy
  rw [WithTop.coe_le_coe]
  apply dd_ge_one
  rw [List.mem_toFinset, Z_mem N i (by omega)] at hy; omega

lemma cheapest_ok (N : ℕ) (hN : 5 ≤ N) :
    IsCheapestRule (dd (N+1)) (fun m => Z N m) (fun i => ((i : ℕ) : Fin (N+1))) := by
  intro i hi1 hi2 x hx
  simp only at hx ⊢
  have hxv : i ≤ x.val := by rw [Z_mem N i (by omega)] at hx; omega
  unfold insCost
  have hA : (Finset.range ((Z N i).length + 1)).inf' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
      (fun pos => cycleLength (dd (N+1)) ((Z N i).insertIdx pos ((i:ℕ) : Fin (N+1))))
      ≤ cycleLength (dd (N+1)) (Z N i) + 2 := by
    refine le_trans (Finset.inf'_le _ (Finset.mem_range.mpr (show (i+1)/2 < (Z N i).length + 1 by
      rw [Z_length]; omega))) ?_
    rw [← Z_step N i (by omega), Z_cycle_step N i hN hi1 (by omega)]
  have hB : cycleLength (dd (N+1)) (Z N i) + 2 ≤
      (Finset.range ((Z N i).length + 1)).inf' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
      (fun pos => cycleLength (dd (N+1)) ((Z N i).insertIdx pos x)) := by
    apply Finset.le_inf'
    intro p hp
    exact Z_lb N i hN hi1 (by omega) x hxv p (by simp at hp; omega)
  linarith

/-! ## part D : k-optimality -/

def chi (n j a b : ℕ) : ℕ :=
  if n < 2 * ad a b then (if (a < j ↔ b < j) then 1 else 0) else (if (a < j ↔ b < j) then 0 else 1)
def wi (n a b : ℕ) : ℕ := if n < 2 * ad a b then 1 else 0

lemma card_cross (n a b : ℕ) :
    ((Finset.Ico 1 n).filter (fun j => ¬ (a < j ↔ b < j))).card = ad a b ∨ n ≤ max a b := by
  by_cases hn : max a b < n
  · left
    unfold ad
    split_ifs with h
    · rw [show (Finset.Ico 1 n).filter (fun j => ¬ (a < j ↔ b < j)) = Finset.Ioc a b by
        ext j; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc]; omega]
      simp
    · rw [show (Finset.Ico 1 n).filter (fun j => ¬ (a < j ↔ b < j)) = Finset.Ioc b a by
        ext j; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc]; omega]
      simp
  · right; omega

lemma edge_id (n a b : ℕ) (ha : a < n) (hb : b < n) :
    dN n a b = ∑ j ∈ Finset.Ico 1 n, chi n j a b + wi n a b := by
  have hc : ((Finset.Ico 1 n).filter (fun j => ¬ (a < j ↔ b < j))).card = ad a b := by
    rcases card_cross n a b with h | h
    · exact h
    · omega
  have htot := Finset.card_filter_add_card_filter_not (s := Finset.Ico 1 n) (fun j => (a < j ↔ b < j))
  simp only [Nat.card_Ico] at htot
  have had : ad a b < n := by unfold ad; split_ifs <;> omega
  unfold chi wi
  by_cases hw : n < 2 * ad a b
  · simp only [hw, if_true]
    rw [Finset.sum_boole]; simp only [Nat.cast_id]
    unfold dN; omega
  · simp only [hw, if_false]
    have : ∀ j, (if (a < j ↔ b < j) then 0 else 1) = (if ¬(a < j ↔ b < j) then 1 else 0) := by
      intro j; split_ifs <;> simp_all
    simp only [this]
    rw [Finset.sum_boole]; simp only [Nat.cast_id]
    unfold dN; omega

lemma chi_zmod (n j a b : ℕ) : ((chi n j a b : ℕ) : ZMod 2) =
    (if a < j then 1 else 0) + (if b < j then 1 else 0) + ((wi n a b : ℕ) : ZMod 2) := by
  unfold chi wi; split_ifs <;> simp_all <;> decide

lemma parity (N : ℕ) (τ : Equiv.Perm (Fin (N+1))) (j : ℕ) :
    ((∑ i, chi (N+1) j (τ i).val (τ (finRotate _ i)).val : ℕ) : ZMod 2) =
    ((∑ i, wi (N+1) (τ i).val (τ (finRotate _ i)).val : ℕ) : ZMod 2) := by
  rw [Nat.cast_sum, Nat.cast_sum]
  simp only [chi_zmod, Finset.sum_add_distrib]
  have : ∑ i, (if (τ (finRotate (N+1) i)).val < j then (1 : ZMod 2) else 0)
      = ∑ i, (if (τ i).val < j then (1:ZMod 2) else 0) :=
    Equiv.sum_comp (finRotate (N+1)) (fun i => if (τ i).val < j then (1 : ZMod 2) else 0)
  rw [this, ← two_mul]
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2, zero_mul, zero_add]

lemma cross (N : ℕ) (τ : Equiv.Perm (Fin (N+1))) (P : Fin (N+1) → Prop) (a b : Fin (N+1))
    (ha : P a) (hb : ¬ P b) : ∃ i, P (τ i) ∧ ¬ P (τ (finRotate _ i)) := by
  by_contra H
  push_neg at H
  have hall : ∀ m : ℕ, P (τ (τ.symm a + (m : Fin (N+1)))) := by
    intro m
    induction m with
    | zero => simpa using ha
    | succ m ih =>
      have := H _ ih
      rw [finRotate_succ_apply] at this
      simpa [Nat.cast_succ, add_assoc] using this
  have := hall ((τ.symm b - τ.symm a).val)
  have e : τ.symm a + (((τ.symm b - τ.symm a).val : ℕ) : Fin (N+1)) = τ.symm b := by
    rw [Fin.cast_val_eq_self]; abel
  rw [e] at this
  simp at this
  exact hb this

lemma memL {n : ℕ} (L : List (Fin n)) (p : ℕ) (hp : p + 1 < L.length) :
    s(L[p], L[p+1]) ∈ listEdges L := by
  unfold listEdges
  rw [List.mem_toFinset, List.mem_iff_getElem]
  refine ⟨p, by simp; omega, ?_⟩
  simp only [List.getElem_zipWith, List.getElem_rotate]
  congr 2
  simp [Nat.mod_eq_of_lt hp]

lemma memL_close {n : ℕ} (L : List (Fin n)) (h : 0 < L.length) :
    s(L[L.length - 1], L[0]) ∈ listEdges L := by
  unfold listEdges
  rw [List.mem_toFinset, List.mem_iff_getElem]
  refine ⟨L.length - 1, by simp; omega, ?_⟩
  simp only [List.getElem_zipWith, List.getElem_rotate]
  congr 2
  simp [Nat.sub_add_cancel h]

lemma Z_elem (N : ℕ) (p : ℕ) (hp : p < (Z N (N+1)).length) :
    (Z N (N+1))[p] = ((zz (N+1) p : ℕ) : Fin (N+1)) := by
  apply Fin.ext
  rw [Z_val N (N+1) le_rfl, natCast_val]
  rw [Z_length] at hp
  unfold zz; split_ifs <;> omega

lemma memT (N : ℕ) (p : ℕ) (hp : p + 1 < N + 1) (a b : ℕ)
    (hab : (zz (N+1) p = a ∧ zz (N+1) (p+1) = b) ∨ (zz (N+1) p = b ∧ zz (N+1) (p+1) = a)) :
    s(((a:ℕ) : Fin (N+1)), ((b:ℕ) : Fin (N+1))) ∈ listEdges (Z N (N+1)) := by
  have hl : p + 1 < (Z N (N+1)).length := by rw [Z_length]; exact hp
  have := memL (Z N (N+1)) p hl
  rw [Z_elem, Z_elem] at this
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at this; exact this
  · rw [h1, h2, Sym2.eq_swap] at this; exact this

lemma mem01 (N : ℕ) (hN : 5 ≤ N) :
    s((((0:ℕ)):ℕ) , ((1:ℕ))) = s((0:ℕ), (1:ℕ)) ∧
    s((((0:ℕ):ℕ) : Fin (N+1)), (((1:ℕ):ℕ) : Fin (N+1))) ∈ listEdges (Z N (N+1)) := by
  refine ⟨rfl, ?_⟩
  have hl : 0 < (Z N (N+1)).length := by rw [Z_length]; omega
  have := memL_close (Z N (N+1)) hl
  rw [Z_elem, Z_elem] at this
  have e1 : zz (N+1) ((Z N (N+1)).length - 1) = 1 := by rw [Z_length]; unfold zz; split_ifs <;> omega
  have e0 : zz (N+1) 0 = 0 := by unfold zz; split_ifs <;> omega
  rw [e1, e0, Sym2.eq_swap] at this
  exact this

lemma mem_pair (N : ℕ) (hN : 5 ≤ N) (b : ℕ) (hb2 : 2 ≤ b) (hbN : b ≤ N) :
    s((((b-2:ℕ)) : Fin (N+1)), ((b:ℕ) : Fin (N+1))) ∈ listEdges (Z N (N+1)) := by
  rcases Nat.even_or_odd b with ⟨r, hr⟩ | ⟨r, hr⟩
  · apply memT N (r - 1) (by omega)
    left; unfold zz; constructor <;> split_ifs <;> omega
  · apply memT N (N - r) (by omega)
    right; unfold zz; constructor <;> split_ifs <;> omega

lemma mem_top (N : ℕ) (hN : 5 ≤ N) :
    s((((N-1:ℕ)) : Fin (N+1)), ((N:ℕ) : Fin (N+1))) ∈ listEdges (Z N (N+1)) := by
  apply memT N ((N+2)/2 - 1) (by omega)
  unfold zz
  rcases Nat.even_or_odd N with ⟨r, hr⟩ | ⟨r, hr⟩
  · right; constructor <;> split_ifs <;> omega
  · left; constructor <;> split_ifs <;> omega

def A1 (j : ℕ) : ℕ := if j = 1 then 0 else j - 2
def B2 (N j : ℕ) : ℕ := if j = N then N else j + 1
def t1 (N j : ℕ) : Sym2 (Fin (N+1)) := s(((A1 j : ℕ) : Fin (N+1)), ((j : ℕ) : Fin (N+1)))
def t2 (N j : ℕ) : Sym2 (Fin (N+1)) := s(((j - 1 : ℕ) : Fin (N+1)), ((B2 N j : ℕ) : Fin (N+1)))

lemma sym2_nat (N a b c d : ℕ) (ha : a < N+1) (hb : b < N+1) (hc : c < N+1) (hd : d < N+1) :
    s(((a:ℕ) : Fin (N+1)), ((b:ℕ) : Fin (N+1))) = s(((c:ℕ) : Fin (N+1)), ((d:ℕ) : Fin (N+1))) ↔
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rw [Sym2.eq_iff]
  simp only [Fin.ext_iff, natCast_val N _ ha, natCast_val N _ hb, natCast_val N _ hc,
    natCast_val N _ hd]

lemma t1_mem (N : ℕ) (hN : 5 ≤ N) (j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    t1 N j ∈ listEdges (Z N (N+1)) := by
  unfold t1 A1
  split_ifs with h
  · subst h; exact (mem01 N hN).2
  · exact mem_pair N hN j (by omega) hjN

lemma t2_mem (N : ℕ) (hN : 5 ≤ N) (j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    t2 N j ∈ listEdges (Z N (N+1)) := by
  unfold t2 B2
  split_ifs with h
  · subst h; exact mem_top _ hN
  · have := mem_pair N hN (j+1) (by omega) (by omega)
    rw [show j + 1 - 2 = j - 1 by omega] at this
    exact this

lemma edge_chi (N : ℕ) (hN : 5 ≤ N) (τ : Equiv.Perm (Fin (N+1))) (j a b : ℕ) (hb : b < N+1)
    (haj : a < j) (hjb : j ≤ b) (hab : b ≤ a + 2)
    (hmem : s(((a:ℕ) : Fin (N+1)), ((b:ℕ):Fin (N+1))) ∈ tourEdges τ) :
    ∃ i, s(τ i, τ (finRotate _ i)) = s(((a:ℕ) : Fin (N+1)), ((b:ℕ):Fin (N+1))) ∧
      chi (N+1) j (τ i).val (τ (finRotate _ i)).val = 1 := by
  unfold tourEdges at hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨i, _, hi⟩ := hmem
  refine ⟨i, hi, ?_⟩
  rw [Sym2.eq_iff] at hi
  have ha' := natCast_val N a (by omega)
  have hb' := natCast_val N b hb
  rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, ha', hb'] <;> unfold chi ad <;> split_ifs <;> omega

lemma sum_lb (s : Finset ℕ) (f : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P] (a b : ℕ)
    (h : ∀ j ∈ s, a ≤ f j + b * (if P j then 1 else 0)) :
    a * s.card ≤ ∑ j ∈ s, f j + b * (s.filter P).card := by
  calc a * s.card = ∑ j ∈ s, a := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ j ∈ s, (f j + b * (if P j then 1 else 0)) := Finset.sum_le_sum h
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]; simp

theorem kopt_nat (N k : ℕ) (hN : 5 ≤ N) (hk : 4 * k ≤ N + 1) (τ : Equiv.Perm (Fin (N+1)))
    (hcard : (listEdges (Z N (N+1)) \ tourEdges τ).card = k) :
    2 * N ≤ ∑ i, dN (N+1) (τ i).val (τ (finRotate _ i)).val := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ, c = fun j => ∑ i, chi (N+1) j (τ i).val (τ (finRotate _ i)).val :=
    ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w = ∑ i, wi (N+1) (τ i).val (τ (finRotate _ i)).val := ⟨_, rfl⟩
  have htot : ∑ i, dN (N+1) (τ i).val (τ (finRotate _ i)).val
      = ∑ j ∈ Finset.Ico 1 (N+1), c j + w := by
    rw [Finset.sum_congr rfl (fun i _ => edge_id (N+1) _ _ (τ i).isLt (τ (finRotate _ i)).isLt)]
    rw [Finset.sum_add_distrib, Finset.sum_comm, hc, hw]
  have hpar : ∀ j, c j % 2 = w % 2 := by
    intro j; rw [hc, hw]; exact (ZMod.natCast_eq_natCast_iff' _ _ 2).mp (parity N τ j)
  have hblock : ∀ j ∈ Finset.Ico 1 (N+1), ∀ j' ∈ Finset.Ico 1 (N+1), j < j' → 1 ≤ c j + c j' := by
    intro j hj j' hj' hjj
    rw [Finset.mem_Ico] at hj hj'
    obtain ⟨i, hi1, hi2⟩ := cross N τ (fun y => j ≤ y.val ∧ y.val < j') ⟨j, by omega⟩ 0
      ⟨le_rfl, hjj⟩ (by simp; omega)
    have : 1 ≤ chi (N+1) j (τ i).val (τ (finRotate _ i)).val
        + chi (N+1) j' (τ i).val (τ (finRotate _ i)).val := by
      unfold chi ad; split_ifs <;> omega
    rw [hc]; simp only
    rw [← Finset.sum_add_distrib]
    exact le_trans this (Finset.single_le_sum (f := fun i => chi (N+1) j (τ i).val (τ (finRotate _ i)).val
      + chi (N+1) j' (τ i).val (τ (finRotate _ i)).val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hline : w = 0 → ∀ j ∈ Finset.Ico 1 (N+1), 1 ≤ c j := by
    intro hw0 j hj
    rw [Finset.mem_Ico] at hj
    obtain ⟨i, hi1, hi2⟩ := cross N τ (fun y => y.val < j) 0 ⟨j, by omega⟩ (by simp; omega)
      (by simp)
    have hwi : wi (N+1) (τ i).val (τ (finRotate _ i)).val = 0 := by
      rw [hw] at hw0; exact (Finset.sum_eq_zero_iff.mp hw0) i (Finset.mem_univ _)
    have : 1 ≤ chi (N+1) j (τ i).val (τ (finRotate _ i)).val := by
      unfold wi at hwi; unfold chi; split_ifs at hwi ⊢ <;> omega
    rw [hc]
    exact le_trans this (Finset.single_le_sum (f := fun i => chi (N+1) j (τ i).val (τ (finRotate _ i)).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hboth : ∀ j ∈ Finset.Ico 1 (N+1), t1 N j ∈ tourEdges τ → t2 N j ∈ tourEdges τ → 2 ≤ c j := by
    intro j hj h1 h2
    rw [Finset.mem_Ico] at hj
    obtain ⟨i1, e1, c1⟩ := edge_chi N hN τ j (A1 j) j (by omega) (by unfold A1; split_ifs <;> omega)
      le_rfl (by unfold A1; split_ifs <;> omega) h1
    obtain ⟨i2, e2, c2⟩ := edge_chi N hN τ j (j-1) (B2 N j) (by unfold B2; split_ifs <;> omega)
      (by omega) (by unfold B2; split_ifs <;> omega) (by unfold B2; split_ifs <;> omega) h2
    have hne : i1 ≠ i2 := by
      intro h; subst h
      have := e1.symm.trans e2
      rw [sym2_nat N _ _ _ _ (by unfold A1; split_ifs <;> omega) (by omega) (by omega)
        (by unfold B2; split_ifs <;> omega)] at this
      unfold A1 B2 at this; split_ifs at this <;> omega
    rw [hc]; simp only
    calc 2 = chi (N+1) j (τ i1).val (τ (finRotate _ i1)).val
          + chi (N+1) j (τ i2).val (τ (finRotate _ i2)).val := by rw [c1, c2]
      _ = ∑ i ∈ {i1, i2}, chi (N+1) j (τ i).val (τ (finRotate _ i)).val :=
          (Finset.sum_pair (f := fun i => chi (N+1) j (τ i).val (τ (finRotate _ i)).val) hne).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hM : ((Finset.Ico 1 (N+1)).filter
      (fun j => ¬ (t1 N j ∈ tourEdges τ ∧ t2 N j ∈ tourEdges τ))).card ≤ 2 * k := by
    have hsub : (Finset.Ico 1 (N+1)).filter
        (fun j => ¬ (t1 N j ∈ tourEdges τ ∧ t2 N j ∈ tourEdges τ)) ⊆
        (listEdges (Z N (N+1)) \ tourEdges τ).biUnion (fun e =>
          (Finset.Ico 1 (N+1)).filter (fun j => t1 N j = e) ∪
          (Finset.Ico 1 (N+1)).filter (fun j => t2 N j = e)) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Ico] at hj
      rw [Finset.mem_biUnion]
      by_cases h1 : t1 N j ∈ tourEdges τ
      · have h2 : t2 N j ∉ tourEdges τ := fun h2 => hj.2 ⟨h1, h2⟩
        refine ⟨t2 N j, Finset.mem_sdiff.mpr ⟨t2_mem N hN j hj.1.1 (by omega), h2⟩, ?_⟩
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hj.1, rfl⟩)
      · refine ⟨t1 N j, Finset.mem_sdiff.mpr ⟨t1_mem N hN j hj.1.1 (by omega), h1⟩, ?_⟩
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hj.1, rfl⟩)
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    rw [← hcard]
    calc ∑ e ∈ listEdges (Z N (N+1)) \ tourEdges τ,
          ((Finset.Ico 1 (N+1)).filter (fun j => t1 N j = e) ∪
          (Finset.Ico 1 (N+1)).filter (fun j => t2 N j = e)).card
        ≤ ∑ e ∈ listEdges (Z N (N+1)) \ tourEdges τ, 2 := by
          apply Finset.sum_le_sum
          intro e _
          refine le_trans (Finset.card_union_le _ _) ?_
          have i1 : ((Finset.Ico 1 (N+1)).filter (fun j => t1 N j = e)).card ≤ 1 := by
            apply Finset.card_le_one.mpr
            intro x hx y hy
            simp only [Finset.mem_filter, Finset.mem_Ico] at hx hy
            have := hx.2.trans hy.2.symm
            unfold t1 at this
            rw [sym2_nat N _ _ _ _ (by unfold A1; split_ifs <;> omega) (by omega)
              (by unfold A1; split_ifs <;> omega) (by omega)] at this
            unfold A1 at this; split_ifs at this <;> omega
          have i2 : ((Finset.Ico 1 (N+1)).filter (fun j => t2 N j = e)).card ≤ 1 := by
            apply Finset.card_le_one.mpr
            intro x hx y hy
            simp only [Finset.mem_filter, Finset.mem_Ico] at hx hy
            have := hx.2.trans hy.2.symm
            unfold t2 at this
            rw [sym2_nat N _ _ _ _ (by omega) (by unfold B2; split_ifs <;> omega)
              (by omega) (by unfold B2; split_ifs <;> omega)] at this
            unfold B2 at this; split_ifs at this <;> omega
          omega
      _ = 2 * (listEdges (Z N (N+1)) \ tourEdges τ).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [htot]
  have heta : ∑ j ∈ Finset.Ico 1 (N+1), c j = (Finset.Ico 1 (N+1)).sum c := rfl
  rw [heta]
  have hIco : (Finset.Ico 1 (N+1)).card = N := by simp
  rcases Nat.eq_zero_or_pos w with hw0 | hwpos
  · have := Finset.card_nsmul_le_sum (Finset.Ico 1 (N+1)) c 2 (by
      intro j hj; have := hline hw0 j hj; have := hpar j; rw [hw0] at this; omega)
    rw [hIco, smul_eq_mul] at this; omega
  · by_cases hodd : w % 2 = 1
    · have := sum_lb (Finset.Ico 1 (N+1)) c
        (fun j => ¬ (t1 N j ∈ tourEdges τ ∧ t2 N j ∈ tourEdges τ)) 3 2 (by
          intro j hj
          have hp := hpar j
          by_cases hb : t1 N j ∈ tourEdges τ ∧ t2 N j ∈ tourEdges τ
          · have := hboth j hj hb.1 hb.2; rw [if_neg (not_not.mpr hb)]; omega
          · rw [if_pos hb]; omega)
      rw [hIco] at this; omega
    · have hZ : ((Finset.Ico 1 (N+1)).filter (fun j => c j = 0)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro x hx y hy
        simp only [Finset.mem_filter] at hx hy
        by_contra hxy
        rcases Nat.lt_or_gt_of_ne hxy with h | h
        · have := hblock x hx.1 y hy.1 h; omega
        · have := hblock y hy.1 x hx.1 h; omega
      have := sum_lb (Finset.Ico 1 (N+1)) c (fun j => c j = 0) 2 2 (by
        intro j hj; have hp := hpar j
        by_cases h0 : c j = 0
        · rw [if_pos h0]; omega
        · rw [if_neg h0]; omega)
      rw [hIco] at this; omega

lemma kopt_ok (N k : ℕ) (hN : 5 ≤ N) (hk : 4 * k ≤ N + 1) :
    IsKOptimal (dd (N+1)) k (Z N (N+1)) := by
  intro τ hτ
  rw [Z_cycle N (N+1) hN (by omega) le_rfl]
  unfold tourLength
  simp only [dd_val]
  rw [← Nat.cast_sum]
  have := kopt_nat N k hN hk τ hτ
  have h2 : ((2 * N : ℕ) : ℝ) ≤ ((∑ i, dN (N+1) (τ i).val (τ (finRotate _ i)).val : ℕ) : ℝ) := by
    exact_mod_cast this
  push_cast at h2 ⊢
  linarith

theorem ratio_core (n k : ℕ) (hn : 6 ≤ n) (hk : 4 * k ≤ n) :
    ∃ d : Fin n → Fin n → ℝ, TSPHeuristics.Shared.IsTSPDist d ∧ 0 < TSPHeuristics.Shared.optimal d ∧
      (∃ (T : ℕ → List (Fin n)) (a : ℕ → Fin n), TSPHeuristics.Shared.IsInsertionRun d T a ∧ TSPHeuristics.Shared.IsNearestRule d T a ∧
        IsKOptimal d k (T n) ∧ TSPHeuristics.Shared.cycleLength d (T n) = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d) ∧
      (∃ (T : ℕ → List (Fin n)) (a : ℕ → Fin n), TSPHeuristics.Shared.IsInsertionRun d T a ∧ TSPHeuristics.Shared.IsCheapestRule d T a ∧
        IsKOptimal d k (T n) ∧ TSPHeuristics.Shared.cycleLength d (T n) = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hN : 5 ≤ N := by omega
  have hopt := optimal_dd N (by omega)
  have hcyc : cycleLength (dd (N+1)) (Z N (N+1)) =
      2 * (1 - 1 / (((N+1 : ℕ)) : ℝ)) * optimal (dd (N+1)) := by
    rw [Z_cycle N (N+1) hN (by omega) le_rfl, hopt]
    have : ((N+1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  refine ⟨dd (N+1), dd_tsp _, by rw [hopt]; positivity, ⟨fun m => Z N m, fun i => ((i : ℕ) : Fin (N+1)),
    run_ok N hN, nearest_ok N hN, kopt_ok N k hN hk, hcyc⟩,
    ⟨fun m => Z N m, fun i => ((i : ℕ) : Fin (N+1)), run_ok N hN, cheapest_ok N hN, kopt_ok N k hN hk, hcyc⟩⟩

end TSPHeuristics.KOpt

open TSPHeuristics.KOpt


theorem solution (n k : ℕ) (hn : 6 ≤ n) (hk : 4 * k ≤ n) :
    ∃ d : Fin n → Fin n → ℝ, TSPHeuristics.Shared.IsTSPDist d ∧ 0 < TSPHeuristics.Shared.optimal d ∧
      (∃ (T : ℕ → List (Fin n)) (a : ℕ → Fin n), TSPHeuristics.Shared.IsInsertionRun d T a ∧ TSPHeuristics.Shared.IsNearestRule d T a ∧
        IsKOptimal d k (T n) ∧ TSPHeuristics.Shared.cycleLength d (T n) = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d) ∧
      (∃ (T : ℕ → List (Fin n)) (a : ℕ → Fin n), TSPHeuristics.Shared.IsInsertionRun d T a ∧ TSPHeuristics.Shared.IsCheapestRule d T a ∧
        IsKOptimal d k (T n) ∧ TSPHeuristics.Shared.cycleLength d (T n) = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d) := by
  exact ratio_core n k hn hk
