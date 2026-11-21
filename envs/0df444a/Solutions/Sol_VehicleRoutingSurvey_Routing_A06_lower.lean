-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.A06_lower
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:17:20.266146+00:00
-- url     : https://prove2.me/submissions/1f3da6fe-81ca-4f6a-878a-237740ca9ae8

import Mathlib
import Definitions.Def_VehicleRoutingSurvey_Routing_MetricAlgorithms

namespace Aux_A06_lower

open TSPHeuristics.Shared

section Lists
variable {α : Type} (d : α → α → ℝ)

def pl : α → List α → ℝ
  | _, [] => 0
  | x, y :: r => d x y + pl y r

def lst : α → List α → α
  | x, [] => x
  | _, y :: r => lst y r

def cyc (L : List α) : ℝ := (List.zipWith d L (L.rotate 1)).sum

theorem zip_eq (x0 : α) : ∀ (x : α) (l : List α),
    (List.zipWith d (x :: l) (l ++ [x0])).sum = pl d x l + d (lst x l) x0
  | x, [] => by simp [pl, lst]
  | x, y :: r => by
    have ih := zip_eq x0 y r
    show (List.zipWith d (x :: y :: r) (y :: (r ++ [x0]))).sum = _
    rw [List.zipWith_cons_cons, List.sum_cons, ih]
    simp only [pl, lst]
    ring

theorem rot1 (x : α) (l : List α) : (x :: l).rotate 1 = l ++ [x] := by
  simp

theorem cyc_cons (x : α) (l : List α) : cyc d (x :: l) = pl d x l + d (lst x l) x := by
  unfold cyc
  rw [rot1]
  exact zip_eq d x x l

theorem three (x y z : α) (L : List α) :
    cyc d (x :: y :: z :: L) = cyc d (x :: z :: L) + d x y + d y z - d x z := by
  rw [cyc_cons, cyc_cons]
  simp only [pl, lst]
  ring

end Lists

/-- the metric -/
def dd (m : ℕ) (i j : Fin (m + 1)) : ℝ :=
  if i = j then 0 else
    if i.val = 0 ∨ j.val = 0 ∨ i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val ∨ i.val + j.val + 1 = 2 * m
    then 1 else 2

theorem dd_self (m : ℕ) (i : Fin (m + 1)) : dd m i i = 0 := by
  simp [dd]

theorem dd_one (m : ℕ) (i j : Fin (m + 1)) (h : i.val ≠ j.val)
    (hc : i.val = 0 ∨ j.val = 0 ∨ i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val ∨ i.val + j.val + 1 = 2 * m) :
    dd m i j = 1 := by
  have h' : i ≠ j := fun e => h (congrArg Fin.val e)
  unfold dd
  rw [if_neg h', if_pos hc]

theorem dd_two (m : ℕ) (i j : Fin (m + 1)) (h : i.val ≠ j.val)
    (hc : ¬ (i.val = 0 ∨ j.val = 0 ∨ i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val ∨
      i.val + j.val + 1 = 2 * m)) :
    dd m i j = 2 := by
  have h' : i ≠ j := fun e => h (congrArg Fin.val e)
  unfold dd
  rw [if_neg h', if_neg hc]

theorem dd_ge_one (m : ℕ) (i j : Fin (m + 1)) (h : i ≠ j) : 1 ≤ dd m i j := by
  unfold dd
  rw [if_neg h]
  split_ifs <;> norm_num

theorem dd_le_two (m : ℕ) (i j : Fin (m + 1)) : dd m i j ≤ 2 := by
  unfold dd
  split_ifs <;> norm_num

theorem dd_nonneg (m : ℕ) (i j : Fin (m + 1)) : 0 ≤ dd m i j := by
  unfold dd
  split_ifs <;> norm_num

theorem dd_symm (m : ℕ) (i j : Fin (m + 1)) : dd m i j = dd m j i := by
  by_cases h : i = j
  · subst h; rfl
  · have hv : i.val ≠ j.val := fun e => h (Fin.ext e)
    by_cases hc : i.val = 0 ∨ j.val = 0 ∨ i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val ∨
        i.val + j.val + 1 = 2 * m
    · rw [dd_one m i j hv hc, dd_one m j i (Ne.symm hv) (by omega)]
    · rw [dd_two m i j hv hc, dd_two m j i (Ne.symm hv) (by omega)]

theorem dd_tri (m : ℕ) (i j k : Fin (m + 1)) : dd m i k ≤ dd m i j + dd m j k := by
  by_cases hik : i = k
  · subst hik; rw [dd_self]; linarith [dd_nonneg m i j, dd_nonneg m j i]
  by_cases hij : i = j
  · subst hij; rw [dd_self]; linarith
  by_cases hjk : j = k
  · subst hjk; rw [dd_self]; linarith
  linarith [dd_le_two m i k, dd_ge_one m i j hij, dd_ge_one m j k hjk]

theorem dd_tsp (m : ℕ) : IsTSPDist (dd m) where
  symm := dd_symm m
  nonneg := dd_nonneg m
  triangle := dd_tri m
  diag := dd_self m

/-- the folding permutation: evens up, then odds down -/
def sigf (s k : ℕ) : ℕ := if k ≤ s then 2 * k else 2 * (2 * s + 1 - k) + 1

def sigi (s v : ℕ) : ℕ := if v % 2 = 0 then v / 2 else 2 * s + 1 - (v - 1) / 2

theorem sigf_lt (s k : ℕ) (hk : k < 2 * s + 2) : sigf s k < 2 * s + 2 := by
  unfold sigf; split_ifs <;> omega

theorem sigi_lt (s v : ℕ) (hv : v < 2 * s + 2) : sigi s v < 2 * s + 2 := by
  unfold sigi; split_ifs <;> omega

theorem sigi_sigf (s k : ℕ) (hk : k < 2 * s + 2) : sigi s (sigf s k) = k := by
  unfold sigf sigi; split_ifs <;> omega

theorem sigf_sigi (s v : ℕ) (hv : v < 2 * s + 2) : sigf s (sigi s v) = v := by
  unfold sigf sigi; split_ifs <;> omega

def sig (m s : ℕ) (hm : m = 2 * s + 1) : Equiv.Perm (Fin (m + 1)) where
  toFun k := ⟨sigf s k.val, by have := sigf_lt s k.val (by omega); omega⟩
  invFun v := ⟨sigi s v.val, by have := sigi_lt s v.val (by omega); omega⟩
  left_inv k := Fin.ext (sigi_sigf s k.val (by omega))
  right_inv v := Fin.ext (sigf_sigi s v.val (by omega))

theorem fr_val (m : ℕ) (k : Fin (m + 1)) :
    (finRotate (m + 1) k).val = if k.val = m then 0 else k.val + 1 := by
  rw [finRotate_succ_apply, Fin.val_add_one]
  by_cases h : k = Fin.last m
  · have e : k.val = m := by rw [h, Fin.val_last]
    rw [if_pos h, if_pos e]
  · have e : k.val ≠ m := fun e => h (Fin.ext (by rw [e, Fin.val_last]))
    rw [if_neg h, if_neg e]

theorem sig_term (m s : ℕ) (hm : m = 2 * s + 1) (k : Fin (m + 1)) :
    dd m (sig m s hm k) (sig m s hm (finRotate (m + 1) k)) = 1 := by
  have hk := k.isLt
  have h1 : (sig m s hm k).val = sigf s k.val := rfl
  have h3 : (sig m s hm (finRotate (m + 1) k)).val = sigf s (finRotate (m + 1) k).val := rfl
  rw [fr_val] at h3
  have key : sigf s k.val ≠ sigf s (if k.val = m then 0 else k.val + 1) ∧
      (sigf s k.val = 0 ∨ sigf s (if k.val = m then 0 else k.val + 1) = 0 ∨
        sigf s k.val + 2 ≤ sigf s (if k.val = m then 0 else k.val + 1) ∨
        sigf s (if k.val = m then 0 else k.val + 1) + 2 ≤ sigf s k.val ∨
        sigf s k.val + sigf s (if k.val = m then 0 else k.val + 1) + 1 = 2 * m) := by
    unfold sigf
    split_ifs <;> omega
  apply dd_one
  · rw [h1, h3]; exact key.1
  · rw [h1, h3]; exact key.2

theorem tour_sig (m s : ℕ) (hm : m = 2 * s + 1) :
    tourLength (dd m) (sig m s hm) = (m : ℝ) + 1 := by
  unfold tourLength
  rw [Finset.sum_congr rfl (fun k _ => sig_term m s hm k)]
  simp

theorem tour_pos (m : ℕ) (hm1 : 1 ≤ m) (τ : Equiv.Perm (Fin (m + 1))) :
    0 < tourLength (dd m) τ := by
  unfold tourLength
  have h0 : (finRotate (m + 1) 0).val = 1 := by
    have hz : ¬ ((0 : Fin (m + 1)).val = m) := by rw [Fin.val_zero]; omega
    rw [fr_val, if_neg hz, Fin.val_zero]
  have hne : τ 0 ≠ τ (finRotate (m + 1) 0) := by
    intro e
    have := τ.injective e
    have := congrArg Fin.val this
    rw [h0, Fin.val_zero] at this
    omega
  have h1 := dd_ge_one m _ _ hne
  have h2 : dd m (τ 0) (τ (finRotate (m + 1) 0)) ≤
      ∑ k, dd m (τ k) (τ (finRotate (m + 1) k)) :=
    Finset.single_le_sum (f := fun k => dd m (τ k) (τ (finRotate (m + 1) k)))
      (fun k _ => dd_nonneg m _ _) (Finset.mem_univ 0)
  linarith

/-- vertex with value `j` (mod `m+1`) -/
def vtx (m j : ℕ) : Fin (m + 1) := ⟨j % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

theorem vtx_val (m j : ℕ) (hj : j ≤ m) : (vtx m j).val = j := Nat.mod_eq_of_lt (by omega)

def Lst (m : ℕ) : ℕ → List (Fin (m + 1))
  | 0 => []
  | k + 1 => vtx m (k + 1) :: Lst m k

theorem mem_Lst (m : ℕ) : ∀ k x, x ∈ Lst m k → ∃ j, 1 ≤ j ∧ j ≤ k ∧ x = vtx m j
  | 0, x, hx => by simp [Lst] at hx
  | k + 1, x, hx => by
    simp only [Lst, List.mem_cons] at hx
    rcases hx with h | h
    · exact ⟨k + 1, by omega, le_rfl, h⟩
    · obtain ⟨j, h1, h2, h3⟩ := mem_Lst m k x h
      exact ⟨j, h1, by omega, h3⟩

end Aux_A06_lower

open Aux_A06_lower TSPHeuristics.Shared in
theorem solution :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ (n : ℕ) (d : Fin n → Fin n → ℝ) (T : ℕ → List (Fin n)),
      N ≤ n ∧ 1 ≤ n ∧ TSPHeuristics.Shared.IsTSPDist d ∧
      0 < TSPHeuristics.Shared.optimal d ∧ VehicleRoutingSurvey.Routing.NearestAdditionRun d T ∧
      (2 - ε) * TSPHeuristics.Shared.optimal d < TSPHeuristics.Shared.cycleLength d (T (n - 1)) := by
  intro ε hε N
  obtain ⟨s, hsN, hs1, hsε⟩ : ∃ s : ℕ, N ≤ s ∧ 1 ≤ s ∧ 3 / ε ≤ (s : ℝ) := by
    refine ⟨N + ⌈3 / ε⌉₊ + 1, by omega, by omega, ?_⟩
    have := Nat.le_ceil (3 / ε)
    push_cast
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  set m := 2 * s + 1 with hm
  refine ⟨m + 1, dd m, fun k => vtx m 0 :: Lst m k, by omega, by omega, dd_tsp m, ?_, ?_, ?_⟩
  · unfold optimal
    rw [Finset.lt_inf'_iff]
    intro τ _
    exact tour_pos m (by omega) τ
  · unfold VehicleRoutingSurvey.Routing.NearestAdditionRun
    refine ⟨⟨vtx m 0, rfl⟩, ?_⟩
    intro k hk
    refine ⟨vtx m (k + 1), vtx m 0, 0, ?_, by simp, ?_, by simp, Or.inl (by simp), ?_⟩
    · intro hmem
      rcases List.mem_cons.mp hmem with h | h
      · have := congrArg Fin.val h
        rw [vtx_val m (k + 1) (by omega), vtx_val m 0 (by omega)] at this
        omega
      · obtain ⟨j, h1, h2, h3⟩ := mem_Lst m k _ h
        have := congrArg Fin.val h3
        rw [vtx_val m (k + 1) (by omega), vtx_val m j (by omega)] at this
        omega
    · intro x hx y hy
      have hne : x ≠ y := fun e => hy (e ▸ hx)
      have h1 : dd m (vtx m 0) (vtx m (k + 1)) = 1 := by
        apply dd_one
        · rw [vtx_val m (k + 1) (by omega), vtx_val m 0 (by omega)]; omega
        · left; exact vtx_val m 0 (by omega)
      rw [h1]
      exact dd_ge_one m x y hne
    · show vtx m 0 :: vtx m (k + 1) :: Lst m k = (vtx m 0 :: Lst m k).insertIdx (0 + 1) (vtx m (k + 1))
      rw [List.insertIdx_succ_cons, List.insertIdx_zero]
  · -- cost of the run
    have hd0 : ∀ j, 1 ≤ j → j ≤ m → dd m (vtx m 0) (vtx m j) = 1 := by
      intro j hj1 hj2
      apply dd_one
      · rw [vtx_val m 0 (by omega), vtx_val m j hj2]; omega
      · left; exact vtx_val m 0 (by omega)
    have hstep : ∀ k, k + 2 ≤ m →
        cycleLength (dd m) (vtx m 0 :: Lst m (k + 1 + 1)) =
          cycleLength (dd m) (vtx m 0 :: Lst m (k + 1)) +
            dd m (vtx m (k + 1 + 1)) (vtx m (k + 1)) := by
      intro k hk
      show cyc (dd m) (vtx m 0 :: vtx m (k + 1 + 1) :: vtx m (k + 1) :: Lst m k) =
        cyc (dd m) (vtx m 0 :: vtx m (k + 1) :: Lst m k) + _
      rw [three, hd0 (k + 1 + 1) (by omega) (by omega), hd0 (k + 1) (by omega) (by omega)]
      ring
    have hbase : cycleLength (dd m) (vtx m 0 :: Lst m 1) = 2 := by
      show cyc (dd m) [vtx m 0, vtx m 1] = 2
      rw [cyc_cons]
      simp only [pl, lst]
      rw [hd0 1 le_rfl (by omega), dd_symm, hd0 1 le_rfl (by omega)]
      norm_num
    have hmid : ∀ k, 1 ≤ k → k + 1 ≤ m →
        cycleLength (dd m) (vtx m 0 :: Lst m k) = 2 * (k : ℝ) := by
      intro k hk1 hk2
      induction k with
      | zero => omega
      | succ k ih =>
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · subst h0
          show cycleLength (dd m) (vtx m 0 :: Lst m 1) = 2 * ((1 : ℕ) : ℝ)
          rw [hbase]; norm_num
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          rw [hstep k' (by omega), ih (by omega) (by omega)]
          rw [dd_two]
          · push_cast; ring
          · rw [vtx_val m (k' + 1 + 1) (by omega), vtx_val m (k' + 1) (by omega)]; omega
          · rw [vtx_val m (k' + 1 + 1) (by omega), vtx_val m (k' + 1) (by omega)]; omega
    obtain ⟨s', hs'⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hfinal : cycleLength (dd m) (vtx m 0 :: Lst m m) = 2 * (m : ℝ) - 1 := by
      have e : Lst m m = Lst m (2 * s' + 1 + 1 + 1) := congrArg (Lst m) (by omega)
      rw [e, hstep (2 * s' + 1) (by omega), hmid (2 * s' + 1 + 1) (by omega) (by omega)]
      rw [dd_one]
      · rw [hm, hs']; push_cast; ring
      · rw [vtx_val m (2 * s' + 1 + 1 + 1) (by omega), vtx_val m (2 * s' + 1 + 1) (by omega)]; omega
      · rw [vtx_val m (2 * s' + 1 + 1 + 1) (by omega), vtx_val m (2 * s' + 1 + 1) (by omega)]; omega
    show (2 - ε) * optimal (dd m) < cycleLength (dd m) (vtx m 0 :: Lst m (m + 1 - 1))
    rw [Nat.add_sub_cancel, hfinal]
    have hopt : optimal (dd m) ≤ (m : ℝ) + 1 := by
      have hmem : sig m s hm ∈ (Finset.univ : Finset (Equiv.Perm (Fin (m + 1)))) := Finset.mem_univ _
      have := Finset.inf'_le (tourLength (dd m)) hmem
      rw [tour_sig] at this
      exact this
    have hpos : 0 < optimal (dd m) := by
      unfold optimal
      rw [Finset.lt_inf'_iff]
      intro τ _
      exact tour_pos m (by omega) τ
    have hmR : (m : ℝ) = 2 * (s : ℝ) + 1 := by rw [hm]; push_cast; ring
    have h3 : 3 < ε * ((m : ℝ) + 1) := by
      have h4 := mul_le_mul_of_nonneg_left hsε hε.le
      have h5 : ε * (3 / ε) = 3 := by field_simp
      have h6 : ε * ((m : ℝ) + 1) = 2 * (ε * s) + 2 * ε := by rw [hmR]; ring
      linarith
    by_cases h2 : ε ≤ 2
    · have := mul_le_mul_of_nonneg_left hopt (by linarith : (0 : ℝ) ≤ 2 - ε)
      have e2 : (2 - ε) * ((m : ℝ) + 1) = 2 * (m : ℝ) + 2 - ε * ((m : ℝ) + 1) := by ring
      linarith
    · push_neg at h2
      have : (2 - ε) * optimal (dd m) < 0 := mul_neg_of_neg_of_pos (by linarith) hpos
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
