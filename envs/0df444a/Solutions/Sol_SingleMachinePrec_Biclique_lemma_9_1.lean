-- Prove2me | solution 1 for SingleMachinePrec.Biclique.lemma_9_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:26:13.684134+00:00
-- url     : https://prove2.me/submissions/13fe64e8-5e8e-4c4d-875a-67f0177b298e

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

lemma e52_harm (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hkn : k ≤ n) :
    ∑ j ∈ Finset.Ioc k n, (1 / (j : ℝ)) ≤ Real.log n - Real.log k := by
  induction n, hkn using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ioc_succ_top hm]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (m : ℝ) / ((m : ℝ) + 1) by positivity)
    rw [Real.log_div hm0.ne' (by positivity)] at h1
    have h2 : (m : ℝ) / ((m : ℝ) + 1) - 1 = -(1 / ((m : ℝ) + 1)) := by field_simp; ring
    push_cast
    linarith

lemma e52_sum_bound (n : ℕ) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (t : ℕ → ℝ)
    (ht1 : ∀ j ∈ Finset.Icc 1 n, t j ≤ n)
    (ht2 : ∀ j ∈ Finset.Icc 1 n, t j * (j : ℝ) ≤ a * (n : ℝ) ^ 2) :
    ∑ j ∈ Finset.Icc 1 n, t j ≤ a * (n : ℝ) ^ 2 * (Real.log (1 / a) + 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hIcc : Finset.Icc 1 n = Finset.Ioc 0 n := by ext j; simp; omega
  rw [hIcc] at ht1 ht2 ⊢
  set k : ℕ := max ⌊a * n⌋₊ 1 with hk
  have hk1 : 1 ≤ k := le_max_right _ _
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have han : a * n ≤ n := by nlinarith
  have hkn : k ≤ n := max_le (Nat.floor_le_of_le han) hn
  have hk2 : a * n ≤ 2 * k := by
    have h1 := Nat.lt_floor_add_one (a * n)
    have h2 : (⌊a * n⌋₊ : ℝ) ≤ k := by exact_mod_cast le_max_left _ _
    have h3 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hann : 0 ≤ a * (n : ℝ) ^ 2 := by positivity
  rw [← Finset.sum_Ioc_consecutive t (Nat.zero_le k) hkn]
  -- first part
  have P1 : ∑ j ∈ Finset.Ioc 0 k, t j ≤ a * (n : ℝ) ^ 2 := by
    by_cases hf : 1 ≤ ⌊a * n⌋₊
    · have hkf : k = ⌊a * n⌋₊ := max_eq_left hf
      calc ∑ j ∈ Finset.Ioc 0 k, t j ≤ ∑ j ∈ Finset.Ioc 0 k, (n : ℝ) :=
            Finset.sum_le_sum (fun j hj => ht1 j (by
              simp only [Finset.mem_Ioc] at hj ⊢; omega))
        _ = k * n := by simp
        _ ≤ (a * n) * n := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [hkf]; exact Nat.floor_le (by positivity)
        _ = _ := by ring
    · have hkf : k = 1 := by
        rw [hk]; omega
      rw [hkf]
      have := ht2 1 (by simp; omega)
      simpa using this
  have P2 : ∑ j ∈ Finset.Ioc k n, t j ≤ a * (n : ℝ) ^ 2 * (Real.log n - Real.log k) := by
    calc ∑ j ∈ Finset.Ioc k n, t j ≤ ∑ j ∈ Finset.Ioc k n, (a * (n : ℝ) ^ 2) * (1 / (j : ℝ)) := by
          apply Finset.sum_le_sum
          intro j hj
          simp only [Finset.mem_Ioc] at hj
          have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
          have := ht2 j (by simp only [Finset.mem_Ioc]; omega)
          rw [mul_one_div, le_div_iff₀ hj0]
          exact this
      _ = a * (n : ℝ) ^ 2 * ∑ j ∈ Finset.Ioc k n, (1 / (j : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (e52_harm k hk1 n hkn) hann
  have P3 : Real.log n - Real.log k ≤ Real.log (1 / a) + 1 := by
    have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have : Real.log n ≤ Real.log ((k : ℝ) * 2 * (1 / a)) := by
      apply Real.log_le_log (by positivity)
      rw [mul_one_div, le_div_iff₀ ha0]
      nlinarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)] at this
    linarith
  nlinarith [mul_le_mul_of_nonneg_left P3 hann]

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

lemma e52_exists_block (A : Finset U) (B : Finset V) : ∃ l : List (U ⊕ V), InBlockOrder A B l := by
  let r : U ⊕ V → U ⊕ V → Prop := fun x y => blockRank A B x ≤ blockRank A B y
  haveI : Std.Total r := ⟨fun a b => le_total _ _⟩
  haveI : IsTrans (U ⊕ V) r := ⟨fun a b c => le_trans⟩
  refine ⟨List.insertionSort r (Finset.univ : Finset (U ⊕ V)).toList, ?_, ?_⟩
  · have hp := List.perm_insertionSort r (Finset.univ : Finset (U ⊕ V)).toList
    refine ⟨hp.nodup_iff.2 (Finset.nodup_toList _), fun x => ?_⟩
    rw [hp.mem_iff]; simp
  · exact List.pairwise_insertionSort r _

lemma e52_before_iff (A : Finset U) (B : Finset V) (l : List (U ⊕ V)) (hl : InBlockOrder A B l)
    (u : U) (v : V) :
    l.idxOf (Sum.inl u) < l.idxOf (Sum.inr v) ↔ (u ∉ A ∨ v ∉ B) := by
  have hs := hl.1
  have hmu := e52_mem l hs (Sum.inl u)
  have hmv := e52_mem l hs (Sum.inr v)
  have hne : l.idxOf (Sum.inl u) ≠ l.idxOf (Sum.inr v) := by
    intro h
    exact Sum.inl_ne_inr (e52_idx_inj hmu hmv h)
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have := e52_pw hl.2 hmu hmv h
    simp [blockRank, hc.1, hc.2] at this
  · intro h
    by_contra hc
    have h' : l.idxOf (Sum.inr v) < l.idxOf (Sum.inl u) := by omega
    have := e52_pw hl.2 hmv hmu h'
    rcases h with h | h <;> simp [blockRank, h] at this <;> split_ifs at this <;> omega

theorem e52_upper (E : U → V → Prop) (n : ℕ) (hU : Fintype.card U = n)
    (hV : Fintype.card V = n) (A : Finset U) (B : Finset V) (hAB : IsEdgeBiclique E A B) :
    (∃ l : List (U ⊕ V), InBlockOrder A B l) ∧
      ∀ l : List (U ⊕ V), InBlockOrder A B l →
        LawlerPrec.MinMax.IsFeasible (precSG E) Finset.univ l ∧
          valSG l = (n : ℝ) ^ 2 - (A.card : ℝ) * (B.card : ℝ) := by
  refine ⟨e52_exists_block A B, fun l hl => ⟨⟨hl.1, ?_⟩, ?_⟩⟩
  · refine hl.2.imp ?_
    intro x y hxy hp
    cases x with
    | inl x => cases y <;> simp [precSG] at hp
    | inr x =>
      cases y with
      | inl y =>
        simp only [precSG, not_not] at hp
        by_cases hy : y ∈ A <;> by_cases hx : x ∈ B <;> simp [blockRank, hx, hy] at hxy
        exact hp (hAB y hy x hx)
      | inr y => simp [precSG] at hp
  · have hc : ∀ v : V, (e52cnt l v : ℝ) = (n : ℝ) - (if v ∈ B then (A.card : ℝ) else 0) := by
      intro v
      unfold e52cnt
      have : univ.filter (fun u : U => l.idxOf (Sum.inl u) < l.idxOf (Sum.inr v)) =
          univ.filter (fun u : U => (u ∉ A ∨ v ∉ B)) :=
        Finset.filter_congr (fun u _ => e52_before_iff A B l hl u v)
      rw [this]
      by_cases hv : v ∈ B
      · simp only [hv, not_true_eq_false, or_false, if_true]
        have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset U)) (fun u : U => u ∈ A)
        rw [Finset.card_univ, hU, Finset.filter_mem_eq_inter, Finset.univ_inter] at h1
        have : (n : ℝ) = (A.card : ℝ) + ((univ.filter (fun u : U => u ∉ A)).card : ℝ) := by
          exact_mod_cast h1.symm
        linarith
      · simp only [hv, not_false_eq_true, or_true, if_false, sub_zero]
        rw [Finset.filter_true_of_mem (fun _ _ => trivial)]
        simp [hU]
    rw [e52_val_eq l hl.1]
    simp only [hc]
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_ite_mem, hV]
    ring

theorem e52_main {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (E : U → V → Prop) (n : ℕ) (hU : Fintype.card U = n) (hV : Fintype.card V = n)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hmax : (maxBicliqueValue E : ℝ) = a * (n : ℝ) ^ 2) :
    (∃ l : List (U ⊕ V), IsOptimalSG E l) ∧
      ∀ l : List (U ⊕ V), IsOptimalSG E l →
        (n : ℝ) ^ 2 - a * (n : ℝ) ^ 2 * (Real.log (1 / a) + 2) ≤ valSG l ∧
          valSG l ≤ (n : ℝ) ^ 2 - a * (n : ℝ) ^ 2 := by
  classical
  have hbic0 : IsEdgeBiclique E (∅ : Finset U) (∅ : Finset V) := by
    intro u hu; simp at hu
  -- a feasible schedule exists
  obtain ⟨l0, hl0⟩ := e52_exists_block (∅ : Finset U) (∅ : Finset V)
  have hfeas0 : LawlerPrec.MinMax.IsFeasible (precSG E) Finset.univ l0 :=
    ((e52_upper E n hU hV ∅ ∅ hbic0).2 l0 hl0).1
  -- existence of an optimal schedule
  have hex : ∃ l : List (U ⊕ V), IsOptimalSG E l := by
    set L := (Finset.univ : Finset (U ⊕ V)).toList with hL
    set F := (L.permutations.toFinset).filter
      (fun l => LawlerPrec.MinMax.IsFeasible (precSG E) Finset.univ l) with hF
    have hmemF : ∀ l, LawlerPrec.MinMax.IsFeasible (precSG E) Finset.univ l → l ∈ F := by
      intro l hl
      rw [hF, Finset.mem_filter, List.mem_toFinset, List.mem_permutations]
      refine ⟨?_, hl⟩
      rw [List.perm_ext_iff_of_nodup hl.1.1 (Finset.nodup_toList _)]
      intro x
      rw [Finset.mem_toList]
      exact hl.1.2 x
    have hFne : F.Nonempty := ⟨l0, hmemF l0 hfeas0⟩
    obtain ⟨lm, hlm, hmin⟩ := Finset.exists_min_image F
      (fun l => weightedCompletion procSG weightSG (Finset.univ : Finset (U ⊕ V)) l) hFne
    refine ⟨lm, (Finset.mem_filter.1 hlm).2, fun l' hl' => hmin l' (hmemF l' hl')⟩
  refine ⟨hex, fun l hl => ⟨?_, ?_⟩⟩
  · -- lower bound
    have hfeas : LawlerPrec.MinMax.IsFeasible (precSG E) Finset.univ l := hl.1
    have hid := (e52_value_identity n hU hV l hfeas.1).2.2
    rw [hid]
    have hsum : ∑ i ∈ Finset.Icc 1 n, (vBefore l i : ℝ) ≤
        a * (n : ℝ) ^ 2 * (Real.log (1 / a) + 2) := by
      have hre : ∑ j ∈ Finset.Icc 1 n, (vBefore l (n + 1 - j) : ℝ) =
          ∑ i ∈ Finset.Icc 1 n, (vBefore l i : ℝ) := by
        refine Finset.sum_nbij' (fun j => n + 1 - j) (fun i => n + 1 - i) ?_ ?_ ?_ ?_ ?_
        · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
        · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
        · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
        · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
        · intro j _; rfl
      rw [← hre]
      apply e52_sum_bound n a ha0 ha1
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        have := (e52_prefix E n hU hV a hmax l hfeas (n + 1 - j) (by omega) (by omega)).2
        exact_mod_cast this
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        have := (e52_prefix E n hU hV a hmax l hfeas (n + 1 - j) (by omega) (by omega)).1
        have hc : ((n + 1 - j : ℕ) : ℝ) = (n : ℝ) + 1 - j := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [hc] at this
        have : (n : ℝ) - ((n : ℝ) + 1 - j) + 1 = j := by ring
        calc _ = (vBefore l (n + 1 - j) : ℝ) * ((n : ℝ) - ((n : ℝ) + 1 - j) + 1) := by rw [this]
          _ ≤ _ := by
            have h2 := (e52_prefix E n hU hV a hmax l hfeas (n + 1 - j) (by omega) (by omega)).1
            rw [hc] at h2
            exact h2
    linarith
  · -- upper bound
    obtain ⟨AB, hABm, hABeq⟩ := Finset.exists_mem_eq_sup
      ((Finset.univ : Finset (Finset U × Finset V)).filter
        (fun AB => IsEdgeBiclique E AB.1 AB.2)) ⟨(∅, ∅), by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hbic0⟩
      (fun AB => AB.1.card * AB.2.card)
    have hbic : IsEdgeBiclique E AB.1 AB.2 := (Finset.mem_filter.1 hABm).2
    have hval : AB.1.card * AB.2.card = maxBicliqueValue E := by
      unfold maxBicliqueValue
      exact hABeq.symm
    obtain ⟨l1, hl1⟩ := e52_exists_block AB.1 AB.2
    obtain ⟨hf1, hv1⟩ := (e52_upper E n hU hV AB.1 AB.2 hbic).2 l1 hl1
    have hle : valSG l ≤ valSG l1 := hl.2 l1 hf1
    have hc : ((AB.1.card : ℝ) * (AB.2.card : ℝ)) = a * (n : ℝ) ^ 2 := by
      rw [← hmax, ← hval]; push_cast; ring
    rw [hv1, hc] at hle
    exact hle

end SingleMachinePrec.Biclique

open SingleMachinePrec.Biclique


theorem solution {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (E : U → V → Prop) (n : ℕ) (hU : Fintype.card U = n) (hV : Fintype.card V = n)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hmax : (maxBicliqueValue E : ℝ) = a * (n : ℝ) ^ 2) :
    (∃ l : List (U ⊕ V), IsOptimalSG E l) ∧
      ∀ l : List (U ⊕ V), IsOptimalSG E l →
        (n : ℝ) ^ 2 - a * (n : ℝ) ^ 2 * (Real.log (1 / a) + 2) ≤ valSG l ∧
          valSG l ≤ (n : ℝ) ^ 2 - a * (n : ℝ) ^ 2 := by
  exact e52_main E n hU hV a ha0 ha1 hmax
