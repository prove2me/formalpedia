-- Prove2me | solution 1 for TSPHeuristics.NearCheap.eq_3_7_insert_eq_sum_cost
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:27:07.909097+00:00
-- url     : https://prove2.me/submissions/a337c80c-5f24-4731-b415-4b0aaa7dcb36

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion



namespace TSPHeuristics.NearCheap

open TSPHeuristics.Shared

/-- path sum from x through L to y -/
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

lemma PS_le {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) (k j : Fin n) (B : List (Fin n)) :
    PS d k B j ≤ d k j + PS d j B j := by
  rcases B with _ | ⟨h, B'⟩
  · simp [PS_nil, hd.diag]
  · rw [PS_cons, PS_cons]; linarith [hd.triangle k j h]

lemma insertIdx_split {α : Type*} (A B : List α) (j k : α) :
    (A ++ j :: B).insertIdx (A.length + 1) k = A ++ j :: k :: B := by
  induction A with
  | nil => simp
  | cons x A ih => simp [List.insertIdx_succ_cons, ih]

lemma lemma2_core {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d)
    (T : List (Fin n)) (k j : Fin n) (hj : j ∈ T) :
    insCost d T k ≤ 2 * d k j := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hj
  unfold insCost
  have hmem : A.length + 1 ∈ Finset.range ((A ++ j :: B).length + 1) := by
    simp
  have h1 := Finset.inf'_le (fun pos => cycleLength d ((A ++ j :: B).insertIdx pos k)) hmem
  rw [insertIdx_split] at h1
  have e1 : cycleLength d (A ++ j :: k :: B) = d j k + PS d k (B ++ A) j := by
    rw [cycle_swap, List.cons_append, List.cons_append, cycle_cons, PS_cons]
  have e2 : cycleLength d (A ++ j :: B) = PS d j (B ++ A) j := by
    rw [cycle_swap, List.cons_append, cycle_cons]
  have := PS_le d hd k j (B ++ A)
  rw [hd.symm j k] at e1
  linarith

theorem insertion_cost_eq {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) (k : Fin n)
    (T' : List (Fin n)) (h : IsInsertion d T k T') :
    insCost d T k = cycleLength d T' - cycleLength d T := by
  obtain ⟨_, pos, hpos, rfl, hmin⟩ := h
  unfold insCost
  congr 1
  apply le_antisymm
  · exact Finset.inf'_le (fun pos => cycleLength d (T.insertIdx pos k))
      (Finset.mem_range.mpr (by omega))
  · apply Finset.le_inf'
    intro p hp
    exact hmin p (by simpa [Nat.lt_succ_iff] using hp)

theorem eq37_core {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    cycleLength d (T n) = ∑ i ∈ Finset.Ico 1 n, insCost d (T i) (a i) := by
  have key : ∀ m, 1 ≤ m → m ≤ n → cycleLength d (T m) = ∑ i ∈ Finset.Ico 1 m, insCost d (T i) (a i) := by
    intro m hm1 hmn
    induction m with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0; rw [hrun.1]; simp [cycleLength, hd.diag]
      · rw [Finset.sum_Ico_succ_top hpos, ← ih hpos (by omega),
          insertion_cost_eq d _ _ _ (hrun.2 m hpos (by omega))]
        ring
  exact key n hn le_rfl

theorem nearest_core {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a)
    (hrule : IsNearestRule d T a) :
    ∀ i, 1 ≤ i → i < n → ∀ p ∈ T i, ∀ q, q ∉ T i →
      insCost d (T i) (a i) ≤ 2 * d p q := by
  intro i hi hin p hp q hq
  have hne : (T i).toFinset.Nonempty := ⟨p, by simpa using hp⟩
  obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_inf (T i).toFinset hne (fun x => ((d x (a i) : ℝ) : WithTop ℝ))
  have h1 := hrule i hi hin q hq
  unfold distToTour at h1
  rw [hxe] at h1
  have h2 : (T i).toFinset.inf (fun x => ((d x q : ℝ) : WithTop ℝ)) ≤ ((d p q : ℝ) : WithTop ℝ) :=
    Finset.inf_le (f := fun x => ((d x q : ℝ) : WithTop ℝ)) (by simpa using hp)
  have h3 : d x (a i) ≤ d p q := WithTop.coe_le_coe.mp (h1.trans h2)
  have h4 := lemma2_core d hd (T i) (a i) x (by simpa using hx)
  rw [hd.symm] at h4
  linarith

theorem cheapest_core {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a)
    (hrule : IsCheapestRule d T a) :
    ∀ i, 1 ≤ i → i < n → ∀ p ∈ T i, ∀ q, q ∉ T i →
      insCost d (T i) (a i) ≤ 2 * d p q := by
  intro i hi hin p hp q hq
  have h1 := hrule i hi hin q hq
  have h2 := lemma2_core d hd (T i) q p hp
  rw [hd.symm] at h2
  linarith

end TSPHeuristics.NearCheap

open TSPHeuristics.NearCheap


theorem solution {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : TSPHeuristics.Shared.IsInsertionRun d T a) :
    TSPHeuristics.Shared.cycleLength d (T n) = ∑ i ∈ Finset.Ico 1 n, TSPHeuristics.Shared.insCost d (T i) (a i) := by
  exact eq37_core hn d hd T a hrun
