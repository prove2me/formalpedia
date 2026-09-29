-- Prove2me | solution 1 for TSPHeuristics.KOpt.theorem_6_proof_circle_subtour_k_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:12:58.642002+00:00
-- url     : https://prove2.me/submissions/e8d227f7-02db-4024-9ada-52dbc38b407b

import Mathlib
import Definitions.Def_TSPHeuristics_KOpt_KOptimal
import Definitions.Def_TSPHeuristics_KOpt_CircleInstance

namespace TSPHeuristics.KOpt

lemma aux_k6_fw_eq {n a b : ℕ} (ha : a < n) (hb : b < n) :
    (b + n - a) % n = if a ≤ b then b - a else b + n - a := by
  split_ifs with h
  · rw [show b + n - a = (b - a) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

abbrev aux_k6_arc (n a b j : ℕ) : Prop :=
  if (b + n - a) % n ≤ (a + n - b) % n then (j + n - a) % n < (b + n - a) % n
  else (j + n - b) % n < (a + n - b) % n

lemma aux_k6_arc_parity {n a b t t' : ℕ} (ha : a < n) (hb : b < n) (ht : t < n)
    (ht' : t' = (t + 1) % n) (hab : a ≠ b) :
    (aux_k6_arc n a b t ↔ aux_k6_arc n a b t') ↔ (t' ≠ a ∧ t' ≠ b) := by
  have ht'n : t' < n := by rw [ht']; exact Nat.mod_lt _ (by omega)
  have h' : (t + 1 < n ∧ t' = t + 1) ∨ (t + 1 = n ∧ t' = 0) := by
    rcases Nat.lt_or_ge (t + 1) n with h | h
    · left; exact ⟨h, by rw [ht', Nat.mod_eq_of_lt h]⟩
    · right; refine ⟨by omega, ?_⟩; rw [ht', show t + 1 = n by omega, Nat.mod_self]
  unfold aux_k6_arc
  rw [aux_k6_fw_eq ha hb, aux_k6_fw_eq hb ha, aux_k6_fw_eq ha ht, aux_k6_fw_eq hb ht,
    aux_k6_fw_eq ha ht'n, aux_k6_fw_eq hb ht'n]
  split_ifs <;> omega

lemma aux_k6_arc_conn {n a b j j' : ℕ} (ha : a < n) (hb : b < n) (hj : j < j') (hj' : j' < n)
    (h1 : ¬ aux_k6_arc n a b j) (h2 : ¬ aux_k6_arc n a b j') :
    (j < a ∧ a ≤ j' ↔ j < b ∧ b ≤ j') := by
  unfold aux_k6_arc at h1 h2
  rw [aux_k6_fw_eq ha hb, aux_k6_fw_eq hb ha, aux_k6_fw_eq ha (by omega : j < n),
    aux_k6_fw_eq hb (by omega : j < n)] at h1
  rw [aux_k6_fw_eq ha hb, aux_k6_fw_eq hb ha, aux_k6_fw_eq ha hj',
    aux_k6_fw_eq hb hj'] at h2
  split_ifs at h1 h2 <;> omega

lemma aux_k6_arc_cover {n p q t : ℕ} (hn : 6 ≤ n) (hpt : p ≤ t) (htq : t < q)
    (hqp : q ≤ p + 2) (hq : q < n) :
    aux_k6_arc n p q t ∧ aux_k6_arc n q p t := by
  unfold aux_k6_arc
  rw [aux_k6_fw_eq (by omega : p < n) hq, aux_k6_fw_eq hq (by omega : p < n),
    aux_k6_fw_eq (by omega : p < n) (by omega : t < n), aux_k6_fw_eq hq (by omega : t < n)]
  split_ifs <;> omega

lemma aux_k6_card_le {n : ℕ} (a : ℕ) (ha : a < n) (m : ℕ) :
    (Finset.univ.filter (fun j : Fin n => (j.val + n - a) % n < m)).card ≤ m := by
  calc _ ≤ (Finset.range m).card := by
        apply Finset.card_le_card_of_injOn (fun j : Fin n => (j.val + n - a) % n)
        · intro j hj
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj
          simpa using hj
        · intro j _ j' _ h
          simp only at h
          have h1 := j.isLt; have h2 := j'.isLt
          rw [aux_k6_fw_eq ha h1, aux_k6_fw_eq ha h2] at h
          apply Fin.ext
          split_ifs at h <;> omega
    _ = m := Finset.card_range m

lemma aux_k6_rot_val {n : ℕ} (i : Fin n) : (finRotate n i).val = (i.val + 1) % n := by
  have hi := i.isLt
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [coe_finRotate]
  split_ifs with h
  · subst h; simp
  · have : i.val ≠ m := fun h' => h (Fin.ext h')
    rw [Nat.mod_eq_of_lt (by omega)]

lemma aux_k6_cyc_le {n : ℕ} (a b : Fin n) (m : ℕ) (h1 : a.val ≤ b.val + m) (h2 : b.val ≤ a.val + m) :
    cycDist n a b ≤ m := by
  unfold cycDist
  have ha := a.isLt; have hb := b.isLt
  rw [aux_k6_fw_eq ha hb, aux_k6_fw_eq hb ha]
  exact_mod_cast (show _ ≤ m by split_ifs <;> first | omega | contradiction)

lemma aux_k6_edge_arc {n : ℕ} (hn : 6 ≤ n) (hn0 : 0 < n) (x y : Fin n) (p q t : ℕ)
    (hpt : p ≤ t) (htq : t < q) (hqp : q ≤ p + 2) (hq : q < n)
    (h : s(x, y) = s(circleNode n hn0 p, circleNode n hn0 q)) :
    aux_k6_arc n x.val y.val t := by
  have hpv : (circleNode n hn0 p).val = p := Nat.mod_eq_of_lt (by omega)
  have hqv : (circleNode n hn0 q).val = q := Nat.mod_eq_of_lt hq
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, hpv, hqv]; exact (aux_k6_arc_cover hn hpt htq hqp hq).1
  · rw [h1, h2, hpv, hqv]; exact (aux_k6_arc_cover hn hpt htq hqp hq).2

theorem aux_k6_lower (n k : ℕ) (hn : 6 ≤ n) (hk : 4 * k ≤ n) (hn0 : 0 < n)
    (τ : Equiv.Perm (Fin n)) (L : Finset (Sym2 (Fin n)))
    (hL1 : ∀ j : ℕ, j ≤ n - 2 → s(circleNode n hn0 (j-1), circleNode n hn0 (j+1)) ∈ L)
    (hL2 : ∀ j : ℕ, j ≤ n - 2 →
      s(circleNode n hn0 j, circleNode n hn0 (min (j+2) (n-1))) ∈ L)
    (hLk : (L \ tourEdges τ).card = k) :
    ((2 * n - 2 : ℕ) : ℝ) ≤ TSPHeuristics.Shared.tourLength (cycDist n) τ := by
  have hmk : ∀ x, x < n → (circleNode n hn0 x).val = x := fun x hx => Nat.mod_eq_of_lt hx
  have hrv : ∀ i : Fin n, (finRotate n i).val = (i.val + 1) % n := aux_k6_rot_val
  let P : Fin n → Fin n → Prop := fun i j =>
    aux_k6_arc n (τ i).val (τ (finRotate n i)).val j.val
  let c : Fin n → ℕ := fun j => (Finset.univ.filter (fun i => P i j)).card
  -- Step L
  have hL : ((∑ j, c j : ℕ) : ℝ) ≤ TSPHeuristics.Shared.tourLength (cycDist n) τ := by
    have e : ∑ j, c j = ∑ i, (Finset.univ.filter (fun j => P i j)).card := by
      simp only [c, Finset.card_filter]; exact Finset.sum_comm
    rw [e, Nat.cast_sum]
    unfold TSPHeuristics.Shared.tourLength
    apply Finset.sum_le_sum; intro i _
    have key : ∀ a b : Fin n,
        (Finset.univ.filter (fun j : Fin n => aux_k6_arc n a.val b.val j.val)).card ≤
          min ((a.val + n - b.val) % n) ((b.val + n - a.val) % n) := by
      intro a b
      by_cases h : (b.val + n - a.val) % n ≤ (a.val + n - b.val) % n
      · rw [min_eq_right h]
        simp only [aux_k6_arc, if_pos h]
        exact aux_k6_card_le a.val a.isLt _
      · rw [min_eq_left (by omega)]
        simp only [aux_k6_arc, if_neg h]
        exact aux_k6_card_le b.val b.isLt _
    unfold cycDist
    exact_mod_cast key (τ i) (τ (finRotate n i))
  -- Step P
  have hP : ∀ j, Even (c j + c (finRotate n j)) := by
    intro j
    have e1 : ∑ i : Fin n, (if τ i = finRotate n j then (1:ℕ) else 0) = 1 := by
      rw [Equiv.sum_comp τ (fun x => if x = finRotate n j then (1:ℕ) else 0)]; simp
    have e2 : ∑ i : Fin n, (if τ (finRotate n i) = finRotate n j then (1:ℕ) else 0) = 1 := by
      have := Equiv.sum_comp ((finRotate n).trans τ)
        (fun x => if x = finRotate n j then (1:ℕ) else 0)
      simp only [Equiv.trans_apply] at this
      exact this.trans (by simp)
    have hsum : c j + c (finRotate n j) + (1 + 1) = ∑ i, ((if P i j then 1 else 0) +
        (if P i (finRotate n j) then 1 else 0) + ((if τ i = finRotate n j then 1 else 0) +
        (if τ (finRotate n i) = finRotate n j then 1 else 0))) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2]
      simp only [c, Finset.card_filter]
    have hterm : ∀ i, Even ((if P i j then 1 else 0) + (if P i (finRotate n j) then 1 else 0) +
        ((if τ i = finRotate n j then 1 else 0) +
        (if τ (finRotate n i) = finRotate n j then 1 else 0))) := by
      intro i
      have hne : τ i ≠ τ (finRotate n i) := by
        intro h; have h1 := τ.injective h
        have h2 := congrArg Fin.val h1; rw [hrv] at h2
        have := i.isLt
        rcases Nat.lt_or_ge (i.val + 1) n with h3 | h3
        · rw [Nat.mod_eq_of_lt h3] at h2; omega
        · rw [show i.val + 1 = n by omega, Nat.mod_self] at h2; omega
      have hvne : (τ i).val ≠ (τ (finRotate n i)).val := fun h => hne (Fin.ext h)
      have hpar := aux_k6_arc_parity (τ i).isLt (τ (finRotate n i)).isLt j.isLt (hrv j) hvne
      have hpar' : (P i j ↔ P i (finRotate n j)) ↔
          (¬ τ i = finRotate n j ∧ ¬ τ (finRotate n i) = finRotate n j) := by
        simp only [P]; rw [hpar]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 (by rw [h]), fun h => h2 (by rw [h])⟩
        · rintro ⟨h1, h2⟩
          exact ⟨fun h => h1 (Fin.ext h.symm), fun h => h2 (Fin.ext h.symm)⟩
      by_cases h1 : P i j <;> by_cases h2 : P i (finRotate n j) <;>
        by_cases h3 : τ i = finRotate n j <;>
        by_cases h4 : τ (finRotate n i) = finRotate n j <;>
        simp only [h1, h2, h3, h4, if_true, if_false] at hpar' ⊢ <;>
        first | decide | (exact absurd (h3.trans h4.symm) hne) | simp at hpar'
    have hE := Finset.even_sum _ (fun i (_ : i ∈ Finset.univ) => hterm i)
    rw [← hsum] at hE
    exact (Nat.even_add.mp hE).mpr (by decide)
  -- Step Par
  have hstep : ∀ j, (Even (c (finRotate n j)) ↔ Even (c j)) :=
    fun j => (Nat.even_add.mp (hP j)).symm
  have hrotmk : ∀ m (hm : m + 1 < n), (⟨m+1, hm⟩ : Fin n) = finRotate n ⟨m, by omega⟩ := by
    intro m hm; apply Fin.ext; rw [hrv]; simp only; rw [Nat.mod_eq_of_lt hm]
  have hpar : ∀ m (hm : m < n), (Even (c ⟨m, hm⟩) ↔ Even (c ⟨0, hn0⟩)) := by
    intro m; induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [hrotmk m hm, hstep]; exact ih _
  have hparj : ∀ j : Fin n, (Even (c j) ↔ Even (c ⟨0, hn0⟩)) := fun j => hpar j.val j.isLt
  -- Step G
  let E1 : Fin n → Sym2 (Fin n) := fun j =>
    s(circleNode n hn0 (j.val-1), circleNode n hn0 (j.val+1))
  let E2 : Fin n → Sym2 (Fin n) := fun j =>
    s(circleNode n hn0 j.val, circleNode n hn0 (min (j.val+2) (n-1)))
  let Q : Fin n → Prop := fun j => j.val ≤ n - 2 ∧ E1 j ∈ tourEdges τ ∧ E2 j ∈ tourEdges τ
  have hGc : ∀ j, Q j → 2 ≤ c j := by
    rintro j ⟨hj, h1, h2⟩
    simp only [tourEdges, Finset.mem_image, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨i1, hi1⟩ := h1
    obtain ⟨i2, hi2⟩ := h2
    have hne : i1 ≠ i2 := by
      rintro rfl
      rw [hi1] at hi2
      have a1 := hmk (j.val-1) (by omega); have a2 := hmk (j.val+1) (by omega)
      have a3 := hmk j.val (by omega); have a4 := hmk (min (j.val+2) (n-1)) (by omega)
      rcases Sym2.eq_iff.mp hi2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · have := congrArg Fin.val h4; have := congrArg Fin.val h3; omega
      · have := congrArg Fin.val h4; have := congrArg Fin.val h3; omega
    have hP1 : P i1 j := aux_k6_edge_arc hn hn0 _ _ (j.val - 1) (j.val + 1) j.val
      (by omega) (by omega) (by omega) (by omega) hi1
    have hP2 : P i2 j := aux_k6_edge_arc hn hn0 _ _ j.val (min (j.val+2) (n-1)) j.val
      (by omega) (by omega) (by omega) (by omega) hi2
    calc 2 = ({i1, i2} : Finset (Fin n)).card := (Finset.card_pair hne).symm
      _ ≤ c j := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl
        · exact hP1
        · exact hP2
  have hGcard : n - 1 ≤ (Finset.univ.filter Q).card + 2 * k := by
    let Sx := Finset.univ.filter (fun j : Fin n => j.val ≤ n - 2)
    have hS : n - 1 ≤ Sx.card := by
      have h1 := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (fun j : Fin n => j.val ≤ n - 2)
      have h2 : (Finset.univ.filter (fun j : Fin n => ¬ j.val ≤ n - 2)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        have := a.isLt; have := b.isLt
        exact Fin.ext (by omega)
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      show n - 1 ≤ (Finset.univ.filter (fun j : Fin n => j.val ≤ n - 2)).card
      omega
    let B1 := Sx.filter (fun j => E1 j ∉ tourEdges τ)
    let B2 := Sx.filter (fun j => E2 j ∉ tourEdges τ)
    have hB1 : B1.card ≤ k := by
      rw [← hLk]
      apply Finset.card_le_card_of_injOn E1
      · intro j hj
        simp only [B1, Sx, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe]
        exact ⟨hL1 j.val hj.1, hj.2⟩
      · intro j hj j' hj' h
        simp only [B1, Sx, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
        have a1 := hmk (j.val-1) (by omega); have a2 := hmk (j.val+1) (by omega)
        have a3 := hmk j.val (by omega); have a4 := hmk (min (j.val+2) (n-1)) (by omega)
        have b1 := hmk (j'.val-1) (by omega); have b2 := hmk (j'.val+1) (by omega)
        have b3 := hmk j'.val (by omega); have b4 := hmk (min (j'.val+2) (n-1)) (by omega)
        simp only [E1] at h
        apply Fin.ext
        rcases Sym2.eq_iff.mp h with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · have := congrArg Fin.val h4; have := congrArg Fin.val h3; omega
        · have := congrArg Fin.val h4; have := congrArg Fin.val h3; omega
    have hB2 : B2.card ≤ k := by
      rw [← hLk]
      apply Finset.card_le_card_of_injOn E2
      · intro j hj
        simp only [B2, Sx, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe]
        exact ⟨hL2 j.val hj.1, hj.2⟩
      · intro j hj j' hj' h
        simp only [B2, Sx, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
        have a1 := hmk (j.val-1) (by omega); have a2 := hmk (j.val+1) (by omega)
        have a3 := hmk j.val (by omega); have a4 := hmk (min (j.val+2) (n-1)) (by omega)
        have b1 := hmk (j'.val-1) (by omega); have b2 := hmk (j'.val+1) (by omega)
        have b3 := hmk j'.val (by omega); have b4 := hmk (min (j'.val+2) (n-1)) (by omega)
        simp only [E2] at h
        apply Fin.ext
        rcases Sym2.eq_iff.mp h with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · have := congrArg Fin.val h4; have := congrArg Fin.val h3; omega
        · have := congrArg Fin.val h4; have := congrArg Fin.val h3; omega
    have hsub : Sx ⊆ Finset.univ.filter Q ∪ (B1 ∪ B2) := by
      intro j hj
      simp only [Sx, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, B1, B2, Sx, Q]
      by_cases h1 : E1 j ∈ tourEdges τ <;> by_cases h2 : E2 j ∈ tourEdges τ <;> simp [h1, h2, hj]
    have := Finset.card_le_card hsub
    have := Finset.card_union_le (Finset.univ.filter Q) (B1 ∪ B2)
    have := Finset.card_union_le B1 B2
    omega
  -- Step Conn
  have hzero : ∀ j, c j = 0 → ∀ i, ¬ P i j := by
    intro j hj i hi
    have : i ∈ Finset.univ.filter (fun i => P i j) := by simp [hi]
    simp only [c] at hj
    rw [Finset.card_eq_zero] at hj
    rw [hj] at this; simp at this
  have conn : ∀ j j' : Fin n, j.val < j'.val → c j = 0 → c j' = 0 → False := by
    intro j j' hjj hj hj'
    have h1 := hzero j hj
    have h2 := hzero j' hj'
    let A : Fin n → Prop := fun v => j.val < v.val ∧ v.val ≤ j'.val
    have hA : ∀ i, (A (τ i) ↔ A (τ (finRotate n i))) := fun i =>
      aux_k6_arc_conn (τ i).isLt (τ (finRotate n i)).isLt hjj j'.isLt (h1 i) (h2 i)
    have hAm : ∀ m (hm : m < n), (A (τ ⟨m, hm⟩) ↔ A (τ ⟨0, hn0⟩)) := by
      intro m; induction m with
      | zero => intro _; rfl
      | succ m ih =>
        intro hm
        rw [hrotmk m hm, ← hA]; exact ih _
    have e1 := hAm (τ.symm j').val (τ.symm j').isLt
    have e2 := hAm (τ.symm j).val (τ.symm j).isLt
    simp only [Fin.eta, Equiv.apply_symm_apply, A] at e1 e2
    have := j'.isLt
    omega
  -- Final
  have hfinal : 2 * n - 2 ≤ ∑ j, c j := by
    by_cases h0 : Even (c ⟨0, hn0⟩)
    · have hZ : (Finset.univ.filter (fun j => c j = 0)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        by_contra hab
        rcases Nat.lt_or_gt_of_ne (fun h => hab (Fin.ext h)) with h | h
        · exact conn a b h ha hb
        · exact conn b a h hb ha
      have e : ∑ j, (if c j = 0 then 0 else 2) + ∑ j, (if c j = 0 then 2 else 0) = 2 * n := by
        rw [← Finset.sum_add_distrib]
        rw [Finset.sum_congr rfl (fun j _ => show (if c j = 0 then 0 else 2) +
          (if c j = 0 then 2 else 0) = 2 by split_ifs <;> rfl)]
        simp [mul_comm]
      have e' : ∑ j, (if c j = 0 then 2 else 0) =
          2 * (Finset.univ.filter (fun j => c j = 0)).card := by
        rw [Finset.card_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; split_ifs <;> rfl
      have hle : ∑ j, (if c j = 0 then 0 else 2) ≤ ∑ j, c j := by
        apply Finset.sum_le_sum; intro j _
        split_ifs with h
        · omega
        · have hev := (hparj j).mpr h0
          rcases hev with ⟨r, hr⟩; omega
      omega
    · have hle : ∑ j, (1 + 2 * (if Q j then 1 else 0)) ≤ ∑ j, c j := by
        apply Finset.sum_le_sum; intro j _
        have hodd : ¬ Even (c j) := fun h => h0 ((hparj j).mp h)
        rw [Nat.not_even_iff_odd] at hodd
        rcases hodd with ⟨r, hr⟩
        split_ifs with h
        · have := hGc j h; omega
        · omega
      have e : ∑ j, (1 + 2 * (if Q j then 1 else 0)) = n + 2 * (Finset.univ.filter Q).card := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.card_filter]; simp [Q]
      omega
  calc ((2 * n - 2 : ℕ) : ℝ) ≤ ((∑ j, c j : ℕ) : ℝ) := by exact_mod_cast hfinal
    _ ≤ _ := hL



def aux_k6_g (n i : ℕ) : ℕ := if i = 0 then 0 else if i ≤ n / 2 then 2 * i - 1 else 2 * (n - i)

lemma aux_k6_zip {α β : Type*} (n : ℕ) (f : ℕ → α) (F : α → α → β) :
    List.zipWith F ((List.range n).map f) (((List.range n).map f).rotate 1) =
      (List.range n).map (fun i => F (f i) (f ((i + 1) % n))) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_zipWith, List.getElem_rotate]

lemma aux_k6_seg0 (n : ℕ) (hn0 : 0 < n) :
    (List.finRange n).filter (fun m : Fin n => decide (m.val < n ∧ m.val = 0)) =
      [circleNode n hn0 0] := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · exact (List.pairwise_lt_finRange n).filter _
  · simp
  · intro m
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      List.mem_singleton]
    constructor
    · rintro ⟨_, h⟩; apply Fin.ext; simp [circleNode, h]
    · rintro rfl; simp [circleNode, hn0]

lemma aux_k6_seg1 (n : ℕ) (hn0 : 0 < n) :
    (List.finRange n).filter (fun m : Fin n => decide (m.val < n ∧ Odd m.val)) =
      (List.range (n / 2)).map (fun t => circleNode n hn0 (2 * t + 1)) := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · exact (List.pairwise_lt_finRange n).filter _
  · rw [List.pairwise_map]
    apply List.pairwise_lt_range.imp_of_mem
    intro a b ha hb hab
    simp only [List.mem_range] at ha hb
    rw [Fin.lt_def]; simp only [circleNode]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · intro m
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, List.mem_map,
      List.mem_range]
    have hm := m.isLt
    constructor
    · rintro ⟨_, ho⟩
      rw [Nat.odd_iff] at ho
      refine ⟨m.val / 2, by omega, ?_⟩
      apply Fin.ext; simp only [circleNode]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rintro ⟨t, ht, rfl⟩
      simp only [circleNode]; rw [Nat.mod_eq_of_lt (by omega)]
      exact ⟨by omega, ⟨t, rfl⟩⟩

lemma aux_k6_seg2 (n : ℕ) (hn0 : 0 < n) :
    (List.finRange n).filter (fun m : Fin n => decide (m.val < n ∧ m.val ≠ 0 ∧ Even m.val)) =
      (List.range ((n - 1) / 2)).map (fun t => circleNode n hn0 (2 * t + 2)) := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · exact (List.pairwise_lt_finRange n).filter _
  · rw [List.pairwise_map]
    apply List.pairwise_lt_range.imp_of_mem
    intro a b ha hb hab
    simp only [List.mem_range] at ha hb
    rw [Fin.lt_def]; simp only [circleNode]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · intro m
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, List.mem_map,
      List.mem_range]
    have hm := m.isLt
    constructor
    · rintro ⟨_, h0, he⟩
      rw [Nat.even_iff] at he
      refine ⟨m.val / 2 - 1, by omega, ?_⟩
      apply Fin.ext; simp only [circleNode]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rintro ⟨t, ht, rfl⟩
      simp only [circleNode]; rw [Nat.mod_eq_of_lt (by omega)]
      exact ⟨by omega, by omega, ⟨t + 1, by ring⟩⟩

lemma aux_k6_T (n : ℕ) (hn : 6 ≤ n) (hn0 : 0 < n) :
    circleSubtour n n = (List.range n).map (fun i => circleNode n hn0 (aux_k6_g n i)) := by
  unfold circleSubtour
  rw [aux_k6_seg0 n hn0, aux_k6_seg1 n hn0, aux_k6_seg2 n hn0]
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_append, List.length_map, List.length_range, List.length_reverse,
      List.length_singleton] at h1
    rcases i with _ | i
    · simp [aux_k6_g]
    · rw [List.getElem_map, List.getElem_range]
      simp only [List.append_assoc]
      simp only [List.singleton_append, List.getElem_cons_succ]
      by_cases hi : i < n / 2
      · rw [List.getElem_append_left (by simpa using hi)]
        simp only [List.getElem_map, List.getElem_range]
        congr 1; unfold aux_k6_g; split_ifs <;> first | omega | contradiction
      · rw [List.getElem_append_right (by simpa using hi)]
        simp only [List.getElem_reverse, List.getElem_map, List.getElem_range, List.length_map,
          List.length_range]
        congr 1; unfold aux_k6_g; split_ifs <;> first | omega | contradiction

lemma aux_k6_listEdges (n : ℕ) (f : ℕ → Fin n) :
    listEdges ((List.range n).map f) =
      ((List.range n).map (fun i => s(f i, f ((i + 1) % n)))).toFinset := by
  unfold listEdges; rw [aux_k6_zip]

lemma aux_k6_cycleLength (n : ℕ) (d : Fin n → Fin n → ℝ) (f : ℕ → Fin n) :
    TSPHeuristics.Shared.cycleLength d ((List.range n).map f) =
      ∑ i ∈ Finset.range n, d (f i) (f ((i + 1) % n)) := by
  unfold TSPHeuristics.Shared.cycleLength
  rw [aux_k6_zip, Finset.sum_eq_multiset_sum]; simp [Finset.range_val, Multiset.range]

lemma aux_k6_mem (n : ℕ) (hn : 6 ≤ n) (hn0 : 0 < n) (i : ℕ) (hi : i < n) (x y : ℕ)
    (hx : aux_k6_g n i = x) (hy : aux_k6_g n ((i + 1) % n) = y) :
    s(circleNode n hn0 x, circleNode n hn0 y) ∈ listEdges (circleSubtour n n) := by
  rw [aux_k6_T n hn hn0, aux_k6_listEdges]
  simp only [List.mem_toFinset, List.mem_map, List.mem_range]
  exact ⟨i, hi, by rw [hx, hy]⟩

lemma aux_k6_mem2 (n : ℕ) (hn : 6 ≤ n) (hn0 : 0 < n) (x : ℕ) (hx : x + 2 < n) :
    s(circleNode n hn0 x, circleNode n hn0 (x + 2)) ∈ listEdges (circleSubtour n n) := by
  rcases Nat.even_or_odd x with he | ho
  · rw [Sym2.eq_swap]
    rw [Nat.even_iff] at he
    apply aux_k6_mem n hn hn0 (n - (x + 2) / 2) (by omega)
    · unfold aux_k6_g; split_ifs <;> first | omega | contradiction
    · by_cases hx0 : x = 0
      · subst hx0
        rw [show n - (0 + 2) / 2 + 1 = n by omega, Nat.mod_self]; simp [aux_k6_g]
      · rw [Nat.mod_eq_of_lt (by omega)]; unfold aux_k6_g; split_ifs <;> first | omega | contradiction
  · rw [Nat.odd_iff] at ho
    apply aux_k6_mem n hn hn0 ((x + 1) / 2) (by omega)
    · unfold aux_k6_g; split_ifs <;> first | omega | contradiction
    · rw [Nat.mod_eq_of_lt (by omega)]; unfold aux_k6_g; split_ifs <;> first | omega | contradiction

lemma aux_k6_cycle_le (n : ℕ) (hn : 6 ≤ n) (hn0 : 0 < n) :
    TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n n) ≤ ((2 * n - 2 : ℕ) : ℝ) := by
  rw [aux_k6_T n hn hn0, aux_k6_cycleLength]
  have hg : ∀ m, m < n → aux_k6_g n m < n := by
    intro m hm; unfold aux_k6_g; split_ifs <;> first | omega | contradiction
  have hb : ∀ i ∈ Finset.range n, cycDist n (circleNode n hn0 (aux_k6_g n i))
      (circleNode n hn0 (aux_k6_g n ((i + 1) % n))) ≤
        (2 : ℝ) - (if i = 0 then 1 else 0) - (if i = n / 2 then 1 else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hv1 : (circleNode n hn0 (aux_k6_g n i)).val = aux_k6_g n i :=
      Nat.mod_eq_of_lt (hg i hi)
    have hv2 : (circleNode n hn0 (aux_k6_g n ((i + 1) % n))).val = aux_k6_g n ((i + 1) % n) :=
      Nat.mod_eq_of_lt (hg _ (Nat.mod_lt _ hn0))
    have hgg : aux_k6_g n i ≤ aux_k6_g n ((i + 1) % n) + (if i = 0 ∨ i = n / 2 then 1 else 2) ∧
        aux_k6_g n ((i + 1) % n) ≤ aux_k6_g n i + (if i = 0 ∨ i = n / 2 then 1 else 2) := by
      by_cases hin : i + 1 = n
      · rw [hin, Nat.mod_self]; unfold aux_k6_g; split_ifs <;> first | omega | contradiction
      · rw [Nat.mod_eq_of_lt (by omega)]; unfold aux_k6_g; split_ifs <;> first | omega | contradiction
    have key := aux_k6_cyc_le (circleNode n hn0 (aux_k6_g n i))
      (circleNode n hn0 (aux_k6_g n ((i + 1) % n))) (if i = 0 ∨ i = n / 2 then 1 else 2)
      (by rw [hv1, hv2]; exact hgg.1) (by rw [hv1, hv2]; exact hgg.2)
    refine key.trans (le_of_eq ?_)
    have : (0:ℕ) ≠ n / 2 := by omega
    by_cases h0 : i = 0
    · subst h0; simp [this]; norm_num
    · by_cases h2 : i = n / 2
      · simp [h0, h2, show ¬ n ≤ 1 by omega] <;> norm_num
      · simp [h0, h2]
  calc _ ≤ ∑ i ∈ Finset.range n,
        ((2 : ℝ) - (if i = 0 then 1 else 0) - (if i = n / 2 then 1 else 0)) :=
        Finset.sum_le_sum hb
    _ = 2 * n - 1 - 1 := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        simp [Finset.sum_ite_eq', hn0, show n / 2 < n by omega] <;> ring
    _ = ((2 * n - 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring

end TSPHeuristics.KOpt

open TSPHeuristics.KOpt

theorem solution (n k : ℕ) (hn : 6 ≤ n) (hk : 4 * k ≤ n) :
    IsKOptimal (cycDist n) k (circleSubtour n n) := by
  have hn0 : 0 < n := by omega
  intro τ hτ
  refine (aux_k6_cycle_le n hn hn0).trans ?_
  apply aux_k6_lower n k hn hk hn0 τ (listEdges (circleSubtour n n)) _ _ hτ
  · intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact aux_k6_mem n hn hn0 0 hn0 0 1 (by simp [aux_k6_g])
        (by rw [Nat.mod_eq_of_lt (by omega)]; unfold aux_k6_g; split_ifs <;> first | omega | contradiction)
    · have := aux_k6_mem2 n hn hn0 (j - 1) (by omega)
      rwa [show j - 1 + 2 = j + 1 by omega] at this
  · intro j hj
    rcases Nat.lt_or_ge j (n - 2) with h | h
    · have := aux_k6_mem2 n hn hn0 j (by omega)
      rwa [show min (j + 2) (n - 1) = j + 2 by omega]
    · rw [show min (j + 2) (n - 1) = n - 1 by omega, show j = n - 2 by omega]
      rcases Nat.even_or_odd n with he | ho
      · rw [Nat.even_iff] at he
        rw [Sym2.eq_swap]
        exact aux_k6_mem n hn hn0 (n / 2) (by omega) (n - 1) (n - 2)
          (by unfold aux_k6_g; split_ifs <;> first | omega | contradiction)
          (by rw [Nat.mod_eq_of_lt (by omega)]; unfold aux_k6_g; split_ifs <;> first | omega | contradiction)
      · rw [Nat.odd_iff] at ho
        exact aux_k6_mem n hn hn0 (n / 2) (by omega) (n - 2) (n - 1)
          (by unfold aux_k6_g; split_ifs <;> first | omega | contradiction)
          (by rw [Nat.mod_eq_of_lt (by omega)]; unfold aux_k6_g; split_ifs <;> first | omega | contradiction)
