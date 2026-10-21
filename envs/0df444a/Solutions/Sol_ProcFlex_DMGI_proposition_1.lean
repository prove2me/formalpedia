-- Prove2me | solution 1 for ProcFlex.DMGI.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T21:04:42.48534+00:00
-- url     : https://prove2.me/submissions/030c2ce8-125f-46f1-aede-fc5ff30da043

import Mathlib
import Definitions.Def_ProcFlex_DMGI_Model
import Theorems.Thm_ProcFlex_DMGI_lemma_3a
import Theorems.Thm_ProcFlex_DMGI_lemma_3b

open Finset ProcFlex.DMGI

namespace PF1

lemma rot_val {n : ℕ} (hn : 0 < n) (j : Fin n) :
    ((finRotate n j) : ℕ) = (j.val + 1) % n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [finRotate_apply, Fin.val_add]
  rcases m with _ | m
  · simp
  · simp

def edges {n : ℕ} (Z : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun j => j ∈ Z ∧ finRotate n j ∈ Z)

lemma edges_sub {n : ℕ} (Z : Finset (Fin n)) : edges Z ⊆ Z := by
  intro j hj; simp [edges, -finRotate_apply] at hj; exact hj.1

lemma edges_mono {n : ℕ} {Z W : Finset (Fin n)} (h : Z ⊆ W) : edges Z ⊆ edges W := by
  intro j hj; simp [edges, -finRotate_apply] at hj ⊢; exact ⟨h hj.1, h hj.2⟩

lemma edges_lt {n : ℕ} (hn : 0 < n) (Z : Finset (Fin n)) (hZ : Z ≠ univ)
    (hne : Z.Nonempty) : (edges Z).card < Z.card := by
  by_contra hcon
  push Not at hcon
  have heq : edges Z = Z := eq_of_subset_of_card_le (edges_sub Z) hcon
  have hcl : ∀ j ∈ Z, finRotate n j ∈ Z := by
    intro j hj
    rw [← heq] at hj; simp [edges, -finRotate_apply] at hj; exact hj.2
  obtain ⟨j0, hj0⟩ := hne
  have hall : ∀ m : ℕ, (⟨(j0.val + m) % n, Nat.mod_lt _ hn⟩ : Fin n) ∈ Z := by
    intro m
    induction m with
    | zero =>
      have : (⟨(j0.val + 0) % n, Nat.mod_lt _ hn⟩ : Fin n) = j0 := by
        ext; simp [Nat.mod_eq_of_lt j0.isLt]
      rw [this]; exact hj0
    | succ m ih =>
      have h1 := hcl _ ih
      have : finRotate n ⟨(j0.val + m) % n, Nat.mod_lt _ hn⟩ =
          (⟨(j0.val + (m + 1)) % n, Nat.mod_lt _ hn⟩ : Fin n) := by
        ext; rw [rot_val hn]; simp [Nat.add_mod, ← add_assoc]
      rwa [this] at h1
  apply hZ
  ext j
  simp only [mem_univ, iff_true]
  have := hall (j.val + n - j0.val)
  have e : (⟨(j0.val + (j.val + n - j0.val)) % n, Nat.mod_lt _ hn⟩ : Fin n) = j := by
    ext
    simp only
    have : j0.val + (j.val + n - j0.val) = j.val + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
  rwa [e] at this

lemma edges_alt {n : ℕ} (c : Fin n → Bool) (hc : ∀ j, c j ≠ c (finRotate n j))
    (Z : Finset (Fin n)) (b : Bool) :
    (edges Z).card ≤ 2 * (Z.filter (fun j => c j = b)).card := by
  set Zb := Z.filter (fun j => c j = b)
  have hsub : edges Z ⊆ Zb ∪ Zb.map (finRotate n).symm.toEmbedding := by
    intro j hj
    simp [edges, -finRotate_apply] at hj
    by_cases hcj : c j = b
    · apply mem_union_left; simp [Zb, hj.1, hcj]
    · apply mem_union_right
      have : c (finRotate n j) = b := by
        have := hc j
        cases hb : b <;> cases h1 : c j <;> cases h2 : c (finRotate n j) <;> simp_all
      simp only [mem_map, Equiv.coe_toEmbedding]
      exact ⟨finRotate n j, by simp [Zb, hj.2, this, -finRotate_apply], by simp [-finRotate_apply]⟩
  calc (edges Z).card ≤ (Zb ∪ Zb.map (finRotate n).symm.toEmbedding).card := card_le_card hsub
    _ ≤ Zb.card + (Zb.map (finRotate n).symm.toEmbedding).card := card_union_le _ _
    _ = 2 * Zb.card := by rw [card_map]; ring

def pos {n : ℕ} (hn : 0 < n) (s : Fin n) (q : ℕ) : Fin n := ⟨(s.val + q) % n, Nat.mod_lt _ hn⟩

def win {n : ℕ} (hn : 0 < n) (s : Fin n) (m : ℕ) : Finset (Fin n) := (range m).image (pos hn s)

lemma pos_inj {n : ℕ} (hn : 0 < n) (s : Fin n) {q q' : ℕ} (hq : q < n) (hq' : q' < n)
    (h : pos hn s q = pos hn s q') : q = q' := by
  have h1 : (s.val + q) % n = (s.val + q') % n := by
    have := congrArg Fin.val h; simpa [pos] using this
  have h2 : q ≡ q' [MOD n] := Nat.ModEq.add_left_cancel' s.val h1
  have := h2; unfold Nat.ModEq at this
  rwa [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hq'] at this

lemma pos_injOn {n : ℕ} (hn : 0 < n) (s : Fin n) {m : ℕ} (hm : m ≤ n) :
    Set.InjOn (pos hn s) (range m : Set ℕ) := by
  intro q hq q' hq' h
  simp at hq hq'
  exact pos_inj hn s (by omega) (by omega) h

lemma win_card {n : ℕ} (hn : 0 < n) (s : Fin n) {m : ℕ} (hm : m ≤ n) :
    (win hn s m).card = m := by
  unfold win; rw [card_image_of_injOn (pos_injOn hn s hm)]; simp

lemma win_filter_card {n : ℕ} (hn : 0 < n) (s : Fin n) {m : ℕ} (hm : m ≤ n)
    (p : Fin n → Prop) [DecidablePred p] :
    ((win hn s m).filter p).card = ((range m).filter (fun q => p (pos hn s q))).card := by
  unfold win
  rw [filter_image, card_image_of_injOn]
  intro q hq q' hq' h
  simp at hq hq'
  exact pos_inj hn s (by omega) (by omega) h

lemma win_edges {n : ℕ} (hn : 0 < n) (s : Fin n) {m : ℕ} (hm : m ≤ n) :
    m - 1 ≤ (edges (win hn s m)).card := by
  have hsub : (range (m - 1)).image (pos hn s) ⊆ edges (win hn s m) := by
    intro j hj
    simp only [mem_image, mem_range] at hj
    obtain ⟨q, hq, rfl⟩ := hj
    simp only [edges, win, mem_filter, mem_univ, true_and, mem_image, mem_range]
    refine ⟨⟨q, by omega, rfl⟩, ⟨q + 1, by omega, ?_⟩⟩
    ext; rw [rot_val hn]; simp [pos, Nat.add_mod, ← add_assoc]
  have := card_le_card hsub
  rw [card_image_of_injOn] at this
  · simpa using this
  · intro q hq q' hq' h
    simp at hq hq'
    exact pos_inj hn s (by omega) (by omega) h

def M (k x y : ℕ) : ℕ := if x + y = 2 * k then 2 * k else min (2 * min x y) (x + y - 1)

lemma M_comm (k x y : ℕ) : M k x y = M k y x := by
  unfold M; rw [add_comm, min_comm x y]

lemma card_tf {n : ℕ} (c : Fin n → Bool) (Z : Finset (Fin n)) :
    (Z.filter (fun j => c j = true)).card + (Z.filter (fun j => c j = false)).card = Z.card := by
  have := card_filter_add_card_filter_not (s := Z) (fun j => c j = true)
  simpa using this

lemma al_bound {k : ℕ} (hk : 1 ≤ k) (c : Fin (2 * k) → Bool)
    (hc : ∀ j, c j ≠ c (finRotate (2 * k) j)) (Z : Finset (Fin (2 * k))) :
    (edges Z).card ≤ M k (Z.filter (fun j => c j = true)).card
      (Z.filter (fun j => c j = false)).card := by
  have hn : 0 < 2 * k := by omega
  have h1 := edges_alt c hc Z true
  have h2 := edges_alt c hc Z false
  have hZ := card_tf c Z
  have hle := card_le_card (edges_sub Z)
  unfold M
  split_ifs with h
  · have : Z.card ≤ 2 * k := by
      calc Z.card ≤ (univ : Finset (Fin (2 * k))).card := card_le_univ Z
        _ = 2 * k := by simp
    omega
  · by_cases he : Z.Nonempty
    · have hne : Z ≠ univ := by
        intro hu; apply h; rw [hZ, hu]; simp
      have := edges_lt hn Z hne he
      omega
    · rw [not_nonempty_iff_eq_empty] at he
      subst he
      simp [edges]

lemma constr_le {k : ℕ} (hk : 1 ≤ k) (c : Fin (2 * k) → Bool)
    (ht : (univ.filter (fun j => c j = true)).card = k)
    (hf : (univ.filter (fun j => c j = false)).card = k)
    (x y : ℕ) (hxy : x ≤ y) (hy : y ≤ k) :
    ∃ Z : Finset (Fin (2 * k)), (Z.filter (fun j => c j = true)).card = x ∧
      (Z.filter (fun j => c j = false)).card = y ∧ M k x y ≤ (edges Z).card := by
  have hn : 0 < 2 * k := by omega
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · -- x = 0 : any y falses
    subst hx0
    obtain ⟨Z, hZs, hZc⟩ := exists_subset_card_eq (s := univ.filter (fun j => c j = false))
      (n := y) (by omega)
    refine ⟨Z, ?_, ?_, ?_⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro j hj; have := hZs hj; simp at this; simp [this]
    · rw [← hZc]; congr 1; ext j; constructor
      · intro hj; exact (mem_filter.mp hj).1
      · intro hj; have := hZs hj; simp at this; exact mem_filter.mpr ⟨hj, this⟩
    · unfold M; split_ifs <;> omega
  rcases eq_or_lt_of_le hxy with hxy' | hxy'
  · subst hxy'
    rcases eq_or_lt_of_le hy with hyk | hyk
    · -- full cycle
      subst hyk
      refine ⟨univ, by simpa using ht, by simpa using hf, ?_⟩
      have : edges (univ : Finset (Fin (2 * x))) = univ := by
        ext j; simp [edges]
      rw [this, card_univ, Fintype.card_fin]; unfold M; split_ifs <;> omega
    · obtain ⟨s, hs⟩ := ProcFlex.DMGI.lemma_3b k hk c ht x hx0 (by omega)
      have hm : 2 * x ≤ 2 * k := by omega
      refine ⟨win hn s (2 * x), ?_, ?_, ?_⟩
      · rw [win_filter_card hn s hm]; exact hs
      · have h1 := card_tf c (win hn s (2 * x))
        rw [win_card hn s hm, win_filter_card hn s hm] at h1
        have : ((range (2 * x)).filter (fun q => c (pos hn s q) = true)).card = x := hs
        omega
      · have := win_edges hn s hm
        unfold M; split_ifs <;> omega
  · -- 1 ≤ x < y ≤ k
    obtain ⟨s, hs⟩ := ProcFlex.DMGI.lemma_3a k hk c ht x hx0 (by omega)
    have hm : 2 * x + 1 ≤ 2 * k := by omega
    set W := win hn s (2 * x + 1) with hW
    have hWt : (W.filter (fun j => c j = true)).card = x := by
      rw [hW, win_filter_card hn s hm]; exact hs
    have hWf : (W.filter (fun j => c j = false)).card = x + 1 := by
      have h1 := card_tf c W
      rw [hW, win_card hn s hm] at h1
      rw [← hW] at h1
      omega
    set F := (univ.filter (fun j => c j = false)) \ W with hF
    have hFc : F.card = k - (x + 1) := by
      rw [hF, card_sdiff]
      have : W ∩ univ.filter (fun j => c j = false) = W.filter (fun j => c j = false) := by
        ext j; simp
      rw [this, hf, hWf]
    obtain ⟨X, hXs, hXc⟩ := exists_subset_card_eq (s := F) (n := y - x - 1) (by omega)
    have hXf : ∀ j ∈ X, c j = false ∧ j ∉ W := by
      intro j hj; have := hXs hj; simp [hF] at this; exact this
    refine ⟨W ∪ X, ?_, ?_, ?_⟩
    · rw [filter_union]
      have : X.filter (fun j => c j = true) = ∅ := by
        rw [filter_eq_empty_iff]; intro j hj; simp [(hXf j hj).1]
      rw [this, union_empty, hWt]
    · rw [filter_union]
      have : X.filter (fun j => c j = false) = X := by
        rw [filter_eq_self]; intro j hj; exact (hXf j hj).1
      rw [this, card_union_of_disjoint, hWf, hXc]
      · omega
      · rw [disjoint_left]; intro j hj hjX; exact (hXf j hjX).2 (mem_filter.mp hj).1
    · have h1 := card_le_card (edges_mono (subset_union_left (s₁ := W) (s₂ := X)))
      have h2 := win_edges hn s hm
      rw [← hW] at h2
      unfold M; split_ifs <;> omega

lemma constr {k : ℕ} (hk : 1 ≤ k) (c : Fin (2 * k) → Bool)
    (ht : (univ.filter (fun j => c j = true)).card = k)
    (hf : (univ.filter (fun j => c j = false)).card = k)
    (x y : ℕ) (hx : x ≤ k) (hy : y ≤ k) :
    ∃ Z : Finset (Fin (2 * k)), (Z.filter (fun j => c j = true)).card = x ∧
      (Z.filter (fun j => c j = false)).card = y ∧ M k x y ≤ (edges Z).card := by
  rcases le_total x y with hxy | hxy
  · exact constr_le hk c ht hf x y hxy hy
  · obtain ⟨Z, h1, h2, h3⟩ := constr_le hk (fun j => !c j) (by simpa using hf)
      (by simpa using ht) y x hxy hx
    refine ⟨Z, by simpa using h2, by simpa using h1, ?_⟩
    rw [M_comm]; exact h3

lemma card_perm {n : ℕ} (π : Equiv.Perm (Fin n)) (p : Fin n → Prop) [DecidablePred p] :
    (univ.filter (fun j => p (π j))).card = (univ.filter p).card := by
  rw [card_filter, card_filter]
  exact Equiv.sum_comp π (fun i => if p i then 1 else 0)

lemma Pbar_cases {k : ℕ} (S : System (2 * k) (2 * k) 2) (r : Fin 3) :
    (r = 0 ∧ Pbar S r = 0) ∨ (r = 1 ∧ Pbar S r = S.P 0) ∨ (r = 2 ∧ Pbar S r = S.P 1) := by
  fin_cases r
  · left; exact ⟨rfl, rfl⟩
  · right; left; exact ⟨rfl, rfl⟩
  · right; right; exact ⟨rfl, rfl⟩

lemma edge_ub {k : ℕ} (S : System (2 * k) (2 * k) 2) (hL : 0 < S.P 0)
    (hLH : S.P 0 < S.P 1) (r s : Fin 3) :
    max (Pbar S r) (Pbar S s) ≤ S.P 0 * (if r = 0 ∧ s = 0 then 0 else 1) +
      (S.P 1 - S.P 0) * ((if r = 2 then 1 else 0) + (if s = 2 then 1 else 0)) := by
  rcases Pbar_cases S r with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
  rcases Pbar_cases S s with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ <;>
  · simp only [h1, h2]; simp +decide [max_def] <;> (try split_ifs) <;> linarith

lemma edge_lb {k : ℕ} (S : System (2 * k) (2 * k) 2) (hL : 0 < S.P 0)
    (hLH : S.P 0 < S.P 1) (r s : Fin 3) (hrs : ¬ (r = 2 ∧ s = 2)) :
    S.P 0 * (if r = 0 ∧ s = 0 then 0 else 1) +
      (S.P 1 - S.P 0) * ((if r = 2 then 1 else 0) + (if s = 2 then 1 else 0)) ≤
      max (Pbar S r) (Pbar S s) := by
  rcases Pbar_cases S r with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
  rcases Pbar_cases S s with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ <;>
  · simp only [h1, h2]; simp +decide [max_def] at hrs ⊢ <;> (try split_ifs) <;> linarith

lemma Pbar_nonneg {k : ℕ} (S : System (2 * k) (2 * k) 2) (hL : 0 < S.P 0)
    (hLH : S.P 0 < S.P 1) (r : Fin 3) : 0 ≤ Pbar S r := by
  rcases Pbar_cases S r with ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ <;> rw [h1] <;> linarith

end PF1

namespace PF1

def cB {k : ℕ} (S : System (2 * k) (2 * k) 2) (π : Equiv.Perm (Fin (2 * k)))
    (j : Fin (2 * k)) : Bool := decide (S.cat (π j) = 1)

def Zl {k : ℕ} (lv : Fin (2 * k) → Fin 3) (π : Equiv.Perm (Fin (2 * k))) :
    Finset (Fin (2 * k)) := univ.filter (fun j => lv (π j) = 0)

noncomputable def cost {k : ℕ} (S : System (2 * k) (2 * k) 2) (lv : Fin (2 * k) → Fin 3)
    (π : Equiv.Perm (Fin (2 * k))) : ℝ :=
  ∑ j, max (Pbar S (lv (π j))) (Pbar S (lv (π (finRotate (2 * k) j))))

lemma fin2_ne1 : ∀ x : Fin 2, ¬ x = 1 ↔ x = 0 := by decide

lemma cB_counts {k : ℕ} (S : System (2 * k) (2 * k) 2) (π : Equiv.Perm (Fin (2 * k)))
    (hcard : (S.s 1).card = k) :
    (univ.filter (fun j => cB S π j = true)).card = k ∧
      (univ.filter (fun j => cB S π j = false)).card = k := by
  have h1 : (univ.filter (fun j => cB S π j = true)).card = k := by
    have := card_perm π (fun i => S.cat i = 1)
    unfold System.s at hcard
    simp only [cB, decide_eq_true_eq]
    rw [this]; exact hcard
  refine ⟨h1, ?_⟩
  have := card_tf (cB S π) univ
  rw [h1, card_univ, Fintype.card_fin] at this; omega

lemma Zl_counts {k : ℕ} (S : System (2 * k) (2 * k) 2) (K : Fin 2 → Fin 3 → ℕ)
    (lv : Fin (2 * k) → Fin 3) (hlv : IsLevelAssignment S K lv) (π : Equiv.Perm (Fin (2 * k))) :
    ((Zl lv π).filter (fun j => cB S π j = true)).card = K 1 0 ∧
      ((Zl lv π).filter (fun j => cB S π j = false)).card = K 0 0 := by
  constructor
  · rw [← hlv.2 1 0 (by decide), ← card_perm π (fun i => S.cat i = 1 ∧ lv i = 0)]
    congr 1; ext j; simp [Zl, cB]; tauto
  · rw [← hlv.2 0 0 (by decide), ← card_perm π (fun i => S.cat i = 0 ∧ lv i = 0)]
    congr 1; ext j; simp [Zl, cB, fin2_ne1]; tauto

lemma N2_eq {k : ℕ} (S : System (2 * k) (2 * k) 2) (hcard : (S.s 1).card = k)
    (K : Fin 2 → Fin 3 → ℕ) (lv : Fin (2 * k) → Fin 3) (hlv : IsLevelAssignment S K lv) :
    (univ.filter (fun i => lv i = 2)).card + K 1 0 + K 1 1 = k := by
  rw [← hlv.2 1 0 (by decide), ← hlv.2 1 1 (by decide)]
  refine Eq.trans ?_ hcard
  unfold System.s
  simp only [card_filter]
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl; intro i _
  have h1 := hlv.1 i
  generalize lv i = r at h1 ⊢
  generalize S.cat i = t at h1 ⊢
  revert r t; decide

lemma phi_sum {k : ℕ} (S : System (2 * k) (2 * k) 2) (lv : Fin (2 * k) → Fin 3)
    (π : Equiv.Perm (Fin (2 * k))) :
    ∑ j, (S.P 0 * (if lv (π j) = 0 ∧ lv (π (finRotate (2 * k) j)) = 0 then 0 else 1) +
      (S.P 1 - S.P 0) * ((if lv (π j) = 2 then 1 else 0) +
        (if lv (π (finRotate (2 * k) j)) = 2 then 1 else 0)))
    = S.P 0 * (((2 * k : ℕ) : ℝ) - ((edges (Zl lv π)).card : ℝ)) +
      (S.P 1 - S.P 0) * (2 * ((univ.filter (fun i => lv i = 2)).card : ℝ)) := by
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_add_distrib]
  have e1 : ∑ j, (if lv (π j) = 0 ∧ lv (π (finRotate (2 * k) j)) = 0 then (0:ℝ) else 1) =
      ((2 * k : ℕ) : ℝ) - (edges (Zl lv π)).card := by
    have hc := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * k))))
      (fun j => lv (π j) = 0 ∧ lv (π (finRotate (2 * k) j)) = 0)
    rw [sum_ite, sum_const_zero, sum_const, nsmul_eq_mul, mul_one, zero_add]
    have : edges (Zl lv π) =
        univ.filter (fun j => lv (π j) = 0 ∧ lv (π (finRotate (2 * k) j)) = 0) := by
      ext j; simp [edges, Zl, -finRotate_apply]
    rw [this]; rw [card_univ, Fintype.card_fin] at hc
    have hc2 := congrArg (Nat.cast : ℕ → ℝ) hc
    push_cast at hc2 ⊢
    linarith
  have e2 : ∑ j, (if lv (π (finRotate (2 * k) j)) = 2 then (1:ℝ) else 0) =
      ∑ j, (if lv (π j) = 2 then (1:ℝ) else 0) :=
    Equiv.sum_comp (finRotate (2 * k)) (fun j => if lv (π j) = 2 then (1:ℝ) else 0)
  have e3 : ∑ j, (if lv (π j) = 2 then (1:ℝ) else 0) =
      ((univ.filter (fun i => lv i = 2)).card : ℝ) := by
    rw [Equiv.sum_comp π (fun i => if lv i = 2 then (1:ℝ) else 0)]; simp [sum_boole]
  rw [e1, e2, e3]; ring

lemma arc_bound {k : ℕ} (S : System (2 * k) (2 * k) 2) (lv : Fin (2 * k) → Fin 3)
    (z : Fin (2 * k) → ℝ) (π : Equiv.Perm (Fin (2 * k)))
    (hz : ∀ a ∈ longChain π, S.p a.2 ≤ beta S (S.cat a.2) (lv a.2) + z a.1) (j : Fin (2 * k)) :
    max (Pbar S (lv (π j))) (Pbar S (lv (π (finRotate (2 * k) j)))) ≤ z j := by
  have h1 := hz (j, π j) (by simp [longChain])
  have h2 := hz (j, π (finRotate (2 * k) j)) (by simp [longChain, -finRotate_apply])
  simp only [System.p, beta] at h1 h2
  exact max_le (by linarith) (by linarith)

end PF1

namespace PF1

lemma exists_lv {k : ℕ} (hk : 1 ≤ k) (S : System (2 * k) (2 * k) 2)
    (hcard : (S.s 1).card = k) (K : Fin 2 → Fin 3 → ℕ)
    (hK0 : K 0 0 ≤ k) (hK1 : K 1 0 + K 1 1 ≤ k) (π : Equiv.Perm (Fin (2 * k))) :
    ∃ lv : Fin (2 * k) → Fin 3, IsLevelAssignment S K lv ∧
      M k (K 1 0) (K 0 0) ≤ (edges (Zl lv π)).card := by
  obtain ⟨ht, hf⟩ := cB_counts S π hcard
  obtain ⟨Z, hZt, hZf, hZe⟩ := constr hk (cB S π) ht hf (K 1 0) (K 0 0) (by omega) hK0
  have h1 : (univ.filter (fun i => S.cat i = 1 ∧ π.symm i ∈ Z)).card = K 1 0 := by
    rw [← hZt, ← card_perm π]; congr 1; ext j; simp [cB]; tauto
  have h2 := card_filter_add_card_filter_not (s := univ.filter (fun i => S.cat i = 1))
    (fun i => π.symm i ∈ Z)
  rw [filter_filter, filter_filter] at h2
  have h3 : (univ.filter (fun i => S.cat i = 1)).card = k := hcard
  have hD : K 1 1 ≤ (univ.filter (fun i => S.cat i = 1 ∧ ¬ π.symm i ∈ Z)).card := by omega
  obtain ⟨Cs, hCsD, hCsc⟩ := exists_subset_card_eq hD
  have hCs : ∀ i ∈ Cs, S.cat i = 1 ∧ π.symm i ∉ Z := fun i hi => by
    have := hCsD hi; simpa using this
  let lv : Fin (2 * k) → Fin 3 := fun i =>
    if π.symm i ∈ Z then 0 else if i ∈ Cs then 1 else if S.cat i = 0 then 1 else 2
  have hlv0 : ∀ i, lv i = 0 ↔ π.symm i ∈ Z := by
    intro i; simp only [lv]; split_ifs <;> simp_all
  have hlv1 : ∀ i, S.cat i = 1 → (lv i = 1 ↔ i ∈ Cs) := by
    intro i hi; simp only [lv]
    split_ifs with g1 g2 g3 <;> simp_all
    · intro h; exact (hCs i h).2 g1
  have hZl : Zl lv π = Z := by ext j; simp [Zl, hlv0]
  refine ⟨lv, ⟨?_, ?_⟩, ?_⟩
  · intro i; simp only [lv]
    split_ifs with g1 g2 g3 <;> simp
    have : ∀ t : Fin 2, ¬ t = 0 → 1 ≤ t.val := by decide
    exact this _ g3
  · have c00 : (univ.filter (fun i => S.cat i = 0 ∧ lv i = 0)).card = K 0 0 := by
      rw [← hZf, ← card_perm π]; congr 1; ext j
      simp only [mem_filter, mem_univ, true_and, hlv0, Equiv.symm_apply_apply, cB]
      simp [fin2_ne1]; tauto
    have c10 : (univ.filter (fun i => S.cat i = 1 ∧ lv i = 0)).card = K 1 0 := by
      rw [← hZt, ← card_perm π]; congr 1; ext j
      simp only [mem_filter, mem_univ, true_and, hlv0, Equiv.symm_apply_apply, cB]
      simp; tauto
    have c11 : (univ.filter (fun i => S.cat i = 1 ∧ lv i = 1)).card = K 1 1 := by
      rw [← hCsc]; congr 1; ext i
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨g1, g2⟩; exact (hlv1 i g1).1 g2
      · intro g; exact ⟨(hCs i g).1, (hlv1 i (hCs i g).1).2 g⟩
    intro t r hrt
    fin_cases t <;> fin_cases r <;> simp at hrt
    · exact c00
    · exact c10
    · exact c11
  · rw [hZl]; exact hZe

end PF1

open PF1 in
theorem solution (k : ℕ) (hk : 1 ≤ k)
    (S : System (2 * k) (2 * k) 2) (hS : S.IsValid)
    (hC : ∀ j, S.C j = 1) (hcard : (S.s 1).card = k)
    (πAL π : Equiv.Perm (Fin (2 * k))) (hAL : IsAlternate S πAL)
    (K : Fin 2 → Fin 3 → ℕ) (hK : InQ S K) :
    dmgi S 0 K (longChain π) ≤ dmgi S 0 K (longChain πAL) := by
  obtain ⟨_, _, _, _, hmono, hpos, _⟩ := hS
  have hL : 0 < S.P 0 := hpos 0
  have hLH : S.P 0 < S.P 1 := hmono (by decide)
  have hs01 : (S.s 0).card + (S.s 1).card = 2 * k := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * k))))
      (fun i => S.cat i = 1)
    rw [card_univ, Fintype.card_fin] at this
    unfold System.s
    rw [add_comm, show univ.filter (fun i => S.cat i = 0) =
      univ.filter (fun i => ¬ S.cat i = 1) by ext; simp [fin2_ne1]]
    exact this
  have hK0 : K 0 0 ≤ k := by
    have := hK 0
    have e : (univ.filter (fun r : Fin 3 => r.val ≤ (0 : Fin 2).val)) = {0} := by decide
    rw [e, sum_singleton] at this; omega
  have hK1 : K 1 0 + K 1 1 ≤ k := by
    have := hK 1
    have e : (univ.filter (fun r : Fin 3 => r.val ≤ (1 : Fin 2).val)) = {0, 1} := by decide
    rw [e, sum_pair (by decide)] at this; omega
  set N := k - K 1 0 - K 1 1 with hNdef
  have hN : ∀ lv, IsLevelAssignment S K lv → (univ.filter (fun i => lv i = 2)).card = N := by
    intro lv hlv; have := N2_eq S hcard K lv hlv; omega
  set V : ℝ := S.P 0 * (((2 * k : ℕ) : ℝ) - (M k (K 1 0) (K 0 0) : ℝ)) +
    (S.P 1 - S.P 0) * (2 * (N : ℝ)) with hV
  -- membership of the canonical cost
  have hmem : ∀ (ρ : Equiv.Perm (Fin (2 * k))) lv, IsLevelAssignment S K lv →
      cost S lv ρ ∈ {v | ∃ (lv : Fin (2 * k) → Fin (2 + 1)) (z : Fin (2 * k) → ℝ),
        IsLevelAssignment S K lv ∧ (∀ j, 0 ≤ z j) ∧
        (∀ a ∈ longChain ρ, S.p a.2 ≤ beta S (S.cat a.2) (lv a.2) + z a.1) ∧
        v = ∑ i, (0 : Fin (2 * k) → ℝ) i * beta S (S.cat i) (lv i) + ∑ j, S.C j * z j} := by
    intro ρ lv hlv
    refine ⟨lv, fun j => max (Pbar S (lv (ρ j))) (Pbar S (lv (ρ (finRotate (2 * k) j)))),
      hlv, fun j => le_max_of_le_left (Pbar_nonneg S hL hLH _), ?_, ?_⟩
    · rintro ⟨j, i⟩ ha
      simp only [longChain, mem_union, mem_image, mem_univ, true_and, Prod.mk.injEq] at ha
      rcases ha with ⟨j', rfl, rfl⟩ | ⟨j', rfl, rfl⟩
      · simp only [System.p, beta]; linarith [le_max_left (Pbar S (lv (ρ j')))
          (Pbar S (lv (ρ (finRotate (2 * k) j'))))]
      · simp only [System.p, beta]; linarith [le_max_right (Pbar S (lv (ρ j')))
          (Pbar S (lv (ρ (finRotate (2 * k) j'))))]
    · simp [hC, cost]
  have hbdd : ∀ ρ : Equiv.Perm (Fin (2 * k)), BddBelow {v | ∃ (lv : Fin (2 * k) → Fin (2 + 1))
        (z : Fin (2 * k) → ℝ),
        IsLevelAssignment S K lv ∧ (∀ j, 0 ≤ z j) ∧
        (∀ a ∈ longChain ρ, S.p a.2 ≤ beta S (S.cat a.2) (lv a.2) + z a.1) ∧
        v = ∑ i, (0 : Fin (2 * k) → ℝ) i * beta S (S.cat i) (lv i) + ∑ j, S.C j * z j} := by
    intro ρ
    refine ⟨0, ?_⟩
    rintro v ⟨lv, z, _, hz, _, rfl⟩
    simp only [Pi.zero_apply, zero_mul, sum_const_zero, zero_add, hC, one_mul]
    exact sum_nonneg (fun j _ => hz j)
  have hub : ∀ lv, IsLevelAssignment S K lv →
      M k (K 1 0) (K 0 0) ≤ (edges (Zl lv π)).card → cost S lv π ≤ V := by
    intro lv hlv he
    calc cost S lv π ≤ _ := sum_le_sum (fun j _ => edge_ub S hL hLH _ _)
      _ = _ := phi_sum S lv π
      _ ≤ V := by
        rw [hV, hN lv hlv]
        have : ((M k (K 1 0) (K 0 0) : ℕ) : ℝ) ≤ ((edges (Zl lv π)).card : ℝ) := by
          exact_mod_cast he
        nlinarith
  have hlb : ∀ lv, IsLevelAssignment S K lv → V ≤ cost S lv πAL := by
    intro lv hlv
    have halt : ∀ j, cB S πAL j ≠ cB S πAL (finRotate (2 * k) j) := by
      intro j
      have := hAL j
      unfold cB
      revert this
      generalize S.cat (πAL j) = x
      generalize S.cat (πAL (finRotate (2 * k) j)) = y
      revert x y; decide
    have he := al_bound hk (cB S πAL) halt (Zl lv πAL)
    obtain ⟨c1, c2⟩ := Zl_counts S K lv hlv πAL
    rw [c1, c2] at he
    have hnot : ∀ j, ¬ (lv (πAL j) = 2 ∧ lv (πAL (finRotate (2 * k) j)) = 2) := by
      intro j ⟨g1, g2⟩
      have a1 := hlv.1 (πAL j)
      have a2 := hlv.1 (πAL (finRotate (2 * k) j))
      have := hAL j
      revert a1 a2 this g1 g2
      generalize S.cat (πAL j) = x
      generalize S.cat (πAL (finRotate (2 * k) j)) = y
      generalize lv (πAL j) = r
      generalize lv (πAL (finRotate (2 * k) j)) = s
      revert x y r s; decide
    calc V ≤ _ := by
          rw [hV, hN lv hlv]
          have : ((edges (Zl lv πAL)).card : ℝ) ≤ ((M k (K 1 0) (K 0 0) : ℕ) : ℝ) := by
            exact_mod_cast he
          nlinarith
      _ = _ := (phi_sum S lv πAL).symm
      _ ≤ cost S lv πAL := sum_le_sum (fun j _ => edge_lb S hL hLH _ _ (hnot j))
  unfold dmgi
  obtain ⟨lv1, hlv1, he1⟩ := exists_lv hk S hcard K hK0 hK1 π
  obtain ⟨lv2, hlv2, _⟩ := exists_lv hk S hcard K hK0 hK1 πAL
  calc sInf _ ≤ cost S lv1 π := csInf_le (hbdd π) (hmem π lv1 hlv1)
    _ ≤ V := hub lv1 hlv1 he1
    _ ≤ _ := by
      apply le_csInf ⟨_, hmem πAL lv2 hlv2⟩
      rintro v ⟨lv, z, hlv, _, harc, rfl⟩
      calc V ≤ cost S lv πAL := hlb lv hlv
        _ ≤ ∑ j, z j := sum_le_sum (fun j _ => arc_bound S lv z πAL harc j)
        _ = _ := by simp [hC]
