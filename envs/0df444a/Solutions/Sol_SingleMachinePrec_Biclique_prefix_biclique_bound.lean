-- Prove2me | solution 1 for SingleMachinePrec.Biclique.prefix_biclique_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:23:10.369847+00:00
-- url     : https://prove2.me/submissions/461575c4-f25b-40e7-8910-2f283e83143c

import Mathlib
import Definitions.Def_SingleMachinePrec_Biclique_SG



namespace SingleMachinePrec.Biclique

open Finset

lemma e52_mem_take_iff {α : Type*} [BEq α] [LawfulBEq α] {l : List α} (hl : l.Nodup) {x : α}
    (hx : x ∈ l) {k : ℕ} : x ∈ l.take k ↔ l.idxOf x < k := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [hl.idxOf_getElem]; omega
  · intro h
    have hlen := List.idxOf_lt_length_of_mem hx
    exact ⟨l.idxOf x, by omega, List.getElem_idxOf hlen⟩

/-- number of `U` jobs before `v` -/
def e52cnt {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (l : List (U ⊕ V)) (v : V) : ℕ :=
  (univ.filter (fun u : U => l.idxOf (Sum.inl u) < l.idxOf (Sum.inr v))).card

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

instance e52_lawfulBEq : LawfulBEq (U ⊕ V) where
  eq_of_beq {a b} h := by
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (by simpa using (show (a == b) = true from h))
      | inr b =>
        have h2 : (Sum.inl a == (Sum.inr b : U ⊕ V)) = false := rfl
        rw [h2] at h; exact absurd h (by decide)
    | inr a =>
      cases b with
      | inl b =>
        have h2 : (Sum.inr a == (Sum.inl b : U ⊕ V)) = false := rfl
        rw [h2] at h; exact absurd h (by decide)
      | inr b => exact congrArg Sum.inr (by simpa using (show (a == b) = true from h))
  rfl {a} := by
    cases a with
    | inl a => exact (show (a == a) = true by simp)
    | inr a => exact (show (a == a) = true by simp)

lemma e52_idxOf_eq (l : List (U ⊕ V)) (x : U ⊕ V) :
    @List.idxOf (U ⊕ V) instBEqOfDecidableEq x l = l.idxOf x := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.idxOf_cons]
    rw [ih]
    have : (@BEq.beq _ instBEqOfDecidableEq b x) = (b == x) := by
      rw [Bool.eq_iff_iff]; simp
    rw [this]

lemma e52_completion_inr (l : List (U ⊕ V)) (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l)
    (v : V) :
    MooreLateJobs.Shared.completionTime (procSG : U ⊕ V → ℝ) l (Sum.inr v) = (e52cnt l v : ℝ) := by
  unfold MooreLateJobs.Shared.completionTime MooreLateJobs.Shared.completionAt
  rw [e52_idxOf_eq]
  have hmem : (Sum.inr v : U ⊕ V) ∈ l := (hl.2 _).2 (mem_univ _)
  have hlen := List.idxOf_lt_length_of_mem hmem
  have hget : l[l.idxOf (Sum.inr v : U ⊕ V)]'hlen = Sum.inr v := List.getElem_idxOf hlen
  rw [List.take_add_one]
  simp only [List.getElem?_eq_getElem hlen, hget]
  generalize hk : l.idxOf (Sum.inr v : U ⊕ V) = k
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  have hnd : (l.take k).Nodup := hl.1.sublist (List.take_sublist _ _)
  rw [← List.sum_toFinset _ hnd]
  have : (l.take k).toFinset = univ.filter (fun x : U ⊕ V => l.idxOf x < k) := by
    ext x
    simp only [List.mem_toFinset, mem_filter, mem_univ, true_and]
    exact e52_mem_take_iff hl.1 ((hl.2 _).2 (mem_univ _))
  rw [this, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, procSG, Finset.sum_const_zero, ite_self, add_zero, e52cnt, hk, Finset.sum_boole]


lemma e52_val_eq (l : List (U ⊕ V)) (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l) :
    valSG l = ∑ v : V, (e52cnt l v : ℝ) := by
  unfold valSG weightedCompletion
  rw [Fintype.sum_sum_type]
  simp only [weightSG, zero_mul, Finset.sum_const_zero, zero_add, one_mul]
  exact Finset.sum_congr rfl (fun v _ => e52_completion_inr l hl v)

lemma e52_cnt_le (l : List (U ⊕ V)) (n : ℕ) (hU : Fintype.card U = n) (v : V) :
    e52cnt l v ≤ n := by
  unfold e52cnt
  calc _ ≤ (univ : Finset U).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := by simp [hU]

lemma e52_vBefore_eq (l : List (U ⊕ V)) (i : ℕ) :
    vBefore l i = (univ.filter (fun v : V => e52cnt l v < i)).card := rfl

lemma e52_abel (s : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 m, (s (i + 1) - s i) * (i : ℝ) = (m : ℝ) * s (m + 1) - ∑ i ∈ Finset.Icc 1 m, s i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

lemma e52_card_Icc (c n : ℕ) (h : c ≤ n) :
    ((Finset.Icc 1 n).filter (fun i => ¬ c < i)).card = c := by
  have : (Finset.Icc 1 n).filter (fun i => ¬ c < i) = Finset.Icc 1 c := by
    ext i; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this]; simp

lemma e52_sum_cnt (l : List (U ⊕ V)) (n : ℕ) (hU : Fintype.card U = n) (hV : Fintype.card V = n) :
    ∑ v : V, (e52cnt l v : ℝ) = (n : ℝ) ^ 2 - ∑ i ∈ Finset.Icc 1 n, (vBefore l i : ℝ) := by
  have h1 : ∀ v : V, (e52cnt l v : ℝ) =
      ∑ i ∈ Finset.Icc 1 n, (if ¬ e52cnt l v < i then (1 : ℝ) else 0) := by
    intro v
    rw [Finset.sum_boole, e52_card_Icc _ _ (e52_cnt_le l n hU v)]
  have h2 : ∀ i : ℕ, (∑ v : V, (if ¬ e52cnt l v < i then (1 : ℝ) else 0)) =
      (n : ℝ) - (vBefore l i : ℝ) := by
    intro i
    rw [Finset.sum_boole, e52_vBefore_eq]
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset V))
      (fun v : V => e52cnt l v < i)
    rw [Finset.card_univ, hV] at this
    have h3 : ((univ.filter (fun v : V => ¬ e52cnt l v < i)).card : ℝ) +
        ((univ.filter (fun v : V => e52cnt l v < i)).card : ℝ) = n := by
      exact_mod_cast (by omega : _ + _ = n)
    linarith
  calc ∑ v : V, (e52cnt l v : ℝ)
      = ∑ v : V, ∑ i ∈ Finset.Icc 1 n, (if ¬ e52cnt l v < i then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl (fun v _ => h1 v)
    _ = ∑ i ∈ Finset.Icc 1 n, ∑ v : V, (if ¬ e52cnt l v < i then (1 : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ i ∈ Finset.Icc 1 n, ((n : ℝ) - (vBefore l i : ℝ)) :=
        Finset.sum_congr rfl (fun i _ => h2 i)
    _ = _ := by
        rw [Finset.sum_sub_distrib]; simp; ring

theorem e52_value_identity (n : ℕ) (hU : Fintype.card U = n) (hV : Fintype.card V = n)
    (l : List (U ⊕ V)) (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l) :
    vBefore l (n + 1) = n ∧
      valSG l = ∑ i ∈ Finset.Icc 1 n, ((vBefore l (i + 1) : ℝ) - (vBefore l i : ℝ)) * (i : ℝ) ∧
      valSG l = (n : ℝ) ^ 2 - ∑ i ∈ Finset.Icc 1 n, (vBefore l i : ℝ) := by
  have h1 : vBefore l (n + 1) = n := by
    rw [e52_vBefore_eq, Finset.filter_true_of_mem (fun v _ => Nat.lt_succ_of_le (e52_cnt_le l n hU v))]
    simp [hV]
  have h3 : valSG l = (n : ℝ) ^ 2 - ∑ i ∈ Finset.Icc 1 n, (vBefore l i : ℝ) := by
    rw [e52_val_eq l hl, e52_sum_cnt l n hU hV]
  refine ⟨h1, ?_, h3⟩
  rw [e52_abel (fun i => (vBefore l i : ℝ)) n, h1, h3]
  ring

lemma e52_pw {R : U ⊕ V → U ⊕ V → Prop} {l : List (U ⊕ V)} (hp : l.Pairwise R)
    {x y : U ⊕ V} (hx : x ∈ l) (hy : y ∈ l) (h : l.idxOf x < l.idxOf y) : R x y := by
  rw [List.pairwise_iff_getElem] at hp
  have hx' := List.idxOf_lt_length_of_mem hx
  have hy' := List.idxOf_lt_length_of_mem hy
  have := hp _ _ hx' hy' h
  simpa [List.getElem_idxOf] using this

lemma e52_idx_inj {l : List (U ⊕ V)} {x y : U ⊕ V} (hx : x ∈ l) (hy : y ∈ l)
    (h : l.idxOf x = l.idxOf y) : x = y := by
  have hx' := List.idxOf_lt_length_of_mem hx
  have hy' := List.idxOf_lt_length_of_mem hy
  have h1 : l[l.idxOf x]'hx' = x := List.getElem_idxOf hx'
  have h2 : l[l.idxOf y]'hy' = y := List.getElem_idxOf hy'
  rw [← h1, ← h2]
  simp [h]

lemma e52_mem (l : List (U ⊕ V)) (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l)
    (x : U ⊕ V) : x ∈ l := (hl.2 x).2 (Finset.mem_univ _)

theorem e52_prefix (E : U → V → Prop) (n : ℕ) (hU : Fintype.card U = n)
    (hV : Fintype.card V = n) (a : ℝ) (hmax : (maxBicliqueValue E : ℝ) = a * (n : ℝ) ^ 2)
    (l : List (U ⊕ V)) (hl : LawlerPrec.MinMax.IsFeasible (precSG E) Finset.univ l)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (vBefore l i : ℝ) * ((n : ℝ) - (i : ℝ) + 1) ≤ a * (n : ℝ) ^ 2 ∧ vBefore l i ≤ n := by
  have hs : MooreLateJobs.Shared.IsSchedule Finset.univ l := hl.1
  have hcard : vBefore l i ≤ n := by
    rw [e52_vBefore_eq]
    calc _ ≤ (univ : Finset V).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = n := by simp [hV]
  refine ⟨?_, hcard⟩
  rw [← hmax]
  rw [e52_vBefore_eq]
  set B := univ.filter (fun v : V => e52cnt l v < i) with hB
  by_cases hne : B.Nonempty
  · obtain ⟨vs, hvs, hmx⟩ := Finset.exists_max_image B (fun v : V => l.idxOf (Sum.inr v)) hne
    set A := univ.filter (fun u : U => l.idxOf (Sum.inr vs) < l.idxOf (Sum.inl u)) with hA
    have bic : IsEdgeBiclique E A B := by
      intro u hu v hv
      rw [hA, Finset.mem_filter] at hu
      have h1 : l.idxOf (Sum.inr v) < l.idxOf (Sum.inl u) :=
        lt_of_le_of_lt (hmx v hv) hu.2
      have h2 := e52_pw hl.2 (e52_mem l hs _) (e52_mem l hs _) h1
      by_contra hE
      exact h2 hE
    have hle : A.card * B.card ≤ maxBicliqueValue E := by
      unfold maxBicliqueValue
      exact Finset.le_sup (f := fun AB : Finset U × Finset V => AB.1.card * AB.2.card) (b := (A, B))
        (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact bic)
    have hsum := Finset.card_filter_add_card_filter_not (s := (univ : Finset U))
      (fun u : U => l.idxOf (Sum.inl u) < l.idxOf (Sum.inr vs))
    rw [Finset.card_univ, hU] at hsum
    have hAeq : univ.filter (fun u : U => ¬ l.idxOf (Sum.inl u) < l.idxOf (Sum.inr vs)) = A := by
      rw [hA]
      apply Finset.filter_congr
      intro u _
      have hne' : l.idxOf (Sum.inl u) ≠ l.idxOf (Sum.inr vs) := by
        intro h
        have := e52_idx_inj (e52_mem l hs _) (e52_mem l hs _) h
        exact Sum.inl_ne_inr this
      omega
    rw [hAeq] at hsum
    have hvs' := (Finset.mem_filter.1 hvs).2
    have hcnt : e52cnt l vs + A.card = n := hsum
    have hAge : (n : ℝ) - (i : ℝ) + 1 ≤ (A.card : ℝ) := by
      have : n + 1 ≤ A.card + i := by omega
      have : ((n : ℝ) + 1 ≤ (A.card : ℝ) + i) := by exact_mod_cast this
      linarith
    have hB0 : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
    calc (B.card : ℝ) * ((n : ℝ) - (i : ℝ) + 1) ≤ (B.card : ℝ) * (A.card : ℝ) :=
          mul_le_mul_of_nonneg_left hAge hB0
      _ = ((A.card * B.card : ℕ) : ℝ) := by push_cast; ring
      _ ≤ _ := by exact_mod_cast hle
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

end SingleMachinePrec.Biclique

open SingleMachinePrec.Biclique


theorem solution {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U]
    [DecidableEq V] (E : U → V → Prop) (n : ℕ) (hU : Fintype.card U = n)
    (hV : Fintype.card V = n) (a : ℝ) (hmax : (maxBicliqueValue E : ℝ) = a * (n : ℝ) ^ 2)
    (l : List (U ⊕ V)) (hl : LawlerPrec.MinMax.IsFeasible (precSG E) Finset.univ l)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (vBefore l i : ℝ) * ((n : ℝ) - (i : ℝ) + 1) ≤ a * (n : ℝ) ^ 2 ∧ vBefore l i ≤ n := by
  exact e52_prefix E n hU hV a hmax l hl i hi1 hin
