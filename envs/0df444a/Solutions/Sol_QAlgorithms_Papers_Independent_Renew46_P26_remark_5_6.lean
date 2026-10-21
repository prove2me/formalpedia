-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P26.remark_5_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T02:13:56.716606+00:00
-- url     : https://prove2.me/submissions/b04e1903-ab7d-42b8-98e5-a51bd8342ce4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26
noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Renew46.P26

theorem g65d_mono {n : ℕ} (T : YoungTableau n) (l l' : Fin n) (h : T.val l ≤ T.val l') :
    l.val ≤ l'.val := by
  obtain ⟨i, hi, he⟩ := T.property.2 (l'.val + 1) (by omega) h ⟨l', by omega, rfl⟩
  have := T.property.1 he
  subst this; omega

theorem g65d_perm_lt {n : ℕ} (i : Adjacent n) (l k : Fin n) (hlk : l.val < k.val)
    (hbad : ¬ (l = i.val ∧ k = nextPosition i)) :
    (adjacentPerm i l).val < (adjacentPerm i k).val := by
  have hn : (nextPosition i).val = i.val.val + 1 := rfl
  simp only [adjacentPerm, Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp_all [Fin.ext_iff] <;> omega

theorem g65d_valid {n : ℕ} (T : YoungTableau n) (i : Adjacent n)
    (hnot : ¬ (T.val i.val ≤ T.val (nextPosition i))) :
    ∀ m : ℕ, m ≤ n → IsLowerSet {b | ∃ k : Fin n, k.val < m ∧ (T.val ∘ adjacentPerm i) k = b} := by
  intro m hm c d hcd hd
  obtain ⟨k, hk, rfl⟩ := hd
  set k' := adjacentPerm i k with hk'
  have hinv : adjacentPerm i k' = k := by simp [hk', adjacentPerm]
  simp only [Function.comp_apply] at hcd
  obtain ⟨l, hl, rfl⟩ := T.property.2 (k'.val + 1) (by omega) hcd ⟨k', by omega, rfl⟩
  refine ⟨adjacentPerm i l, ?_, by simp [adjacentPerm]⟩
  rcases Nat.lt_or_ge l.val k'.val with hlt | hge
  · have : ¬ (l = i.val ∧ k' = nextPosition i) := by
      rintro ⟨rfl, h2⟩; rw [← hk', h2] at hcd; exact hnot hcd
    have := g65d_perm_lt i l k' hlt this
    rw [hinv] at this; omega
  · have : l = k' := Fin.ext (by omega)
    subst this; rw [hinv]; exact hk

/-- the swapped tableau -/
def g65d_swap {n : ℕ} (T : YoungTableau n) (i : Adjacent n)
    (hnot : ¬ (T.val i.val ≤ T.val (nextPosition i))) : YoungTableau n :=
  ⟨T.val ∘ adjacentPerm i, T.property.1.comp (adjacentPerm i).injective, g65d_valid T i hnot⟩

theorem g65d_step {n : ℕ} (T : YoungTableau n) (i : Adjacent n)
    (hnot : ¬ (T.val i.val ≤ T.val (nextPosition i))) : TableauStep T (g65d_swap T i hnot) := by
  have hnot2 : ¬ (T.val (nextPosition i) ≤ T.val i.val) := by
    intro h; have := g65d_mono T _ _ h; simp [nextPosition] at this
  refine ⟨i, ?_, ?_, rfl⟩
  · intro h; rcases le_total (T.val i.val).2 (T.val (nextPosition i)).2 with h' | h'
    · exact hnot (Prod.le_def.mpr ⟨h.le, h'⟩)
    · exact hnot2 (Prod.le_def.mpr ⟨h.ge, h'⟩)
  · intro h; rcases le_total (T.val i.val).1 (T.val (nextPosition i)).1 with h' | h'
    · exact hnot (Prod.le_def.mpr ⟨h', h.le⟩)
    · exact hnot2 (Prod.le_def.mpr ⟨h', h.ge⟩)

theorem g65d_move {n k : ℕ} (hk : k < n) (U : YoungTableau n) :
    ∀ d : ℕ, ∀ (T : YoungTableau n) (j : Fin n), j.val + d = k → T.val j = U.val ⟨k, hk⟩ →
      Finset.univ.image T.val = Finset.univ.image U.val →
      (∀ l : Fin n, k < l.val → T.val l = U.val l) →
      ∃ T' : YoungTableau n, Relation.ReflTransGen TableauStep T T' ∧
        T'.val ⟨k, hk⟩ = U.val ⟨k, hk⟩ ∧ Finset.univ.image T'.val = Finset.univ.image U.val ∧
        (∀ l : Fin n, k < l.val → T'.val l = U.val l) := by
  intro d
  induction d with
  | zero =>
    intro T j hj hTj him hag
    have : j = ⟨k, hk⟩ := Fin.ext (by simpa using hj)
    subst this
    exact ⟨T, Relation.ReflTransGen.refl, hTj, him, hag⟩
  | succ d ih =>
    intro T j hj hTj him hag
    let i : Adjacent n := ⟨j, by omega⟩
    have hnext : (nextPosition i).val = j.val + 1 := rfl
    have hmem : T.val (nextPosition i) ∈ Finset.univ.image U.val := by
      rw [← him]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    obtain ⟨l', -, hl'⟩ := Finset.mem_image.mp hmem
    have hl'k : l'.val ≤ k := by
      by_contra hc
      have h1 := hag l' (by omega)
      rw [hl'] at h1
      have := T.property.1 h1
      rw [this] at hc; omega
    have hnot : ¬ (T.val i.val ≤ T.val (nextPosition i)) := by
      intro hle
      change T.val j ≤ _ at hle
      rw [hTj, ← hl'] at hle
      have h1 := g65d_mono U _ _ hle
      have h2 : l' = ⟨k, hk⟩ := Fin.ext (by simp at h1 ⊢; omega)
      rw [h2, ← hTj] at hl'
      have := T.property.1 hl'
      have := congrArg Fin.val this
      rw [hnext] at this; omega
    set T1 := g65d_swap T i hnot with hT1
    have hT1v : T1.val = T.val ∘ adjacentPerm i := rfl
    have hT1n : T1.val (nextPosition i) = U.val ⟨k, hk⟩ := by
      rw [hT1v, Function.comp_apply, adjacentPerm, Equiv.swap_apply_right]; exact hTj
    have him1 : Finset.univ.image T1.val = Finset.univ.image U.val := by
      rw [← him]; ext b; simp only [Finset.mem_image, Finset.mem_univ, true_and, hT1v,
        Function.comp_apply]
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨_, rfl⟩
      · rintro ⟨a, rfl⟩; exact ⟨adjacentPerm i a, by simp [adjacentPerm]⟩
    have hag1 : ∀ l : Fin n, k < l.val → T1.val l = U.val l := by
      intro l hl
      rw [hT1v, Function.comp_apply, adjacentPerm, Equiv.swap_apply_of_ne_of_ne]
      · exact hag l hl
      · intro h; rw [h] at hl; change k < j.val at hl; omega
      · intro h; rw [h, hnext] at hl; omega
    obtain ⟨T', h1, h2, h3, h4⟩ := ih T1 (nextPosition i) (by rw [hnext]; omega) hT1n him1 hag1
    exact ⟨T', Relation.ReflTransGen.head (g65d_step T i hnot) h1, h2, h3, h4⟩

def g65d_inv {n : ℕ} (U : YoungTableau n) (t : Fin n → ℕ × ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ labelAt U (t p.1) > labelAt U (t p.2))).card

theorem g65d_label_self {n : ℕ} (U : YoungTableau n) (l : Fin n) : labelAt U (U.val l) = l.val := by
  unfold labelAt
  rw [Finset.sum_eq_single l]
  · simp
  · intro i _ hi; rw [if_neg]; intro h; exact hi (U.property.1 h)
  · simp

/-- general counting: `L ∘ swap` has at most one more inversion -/
theorem g65d_cnt_le {n : ℕ} (L : Fin n → ℕ) (i : Adjacent n) :
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ L (adjacentPerm i p.1) > L (adjacentPerm i p.2))).card
      ≤ (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ L p.1 > L p.2)).card + 1 := by
  set A := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ L (adjacentPerm i p.1) > L (adjacentPerm i p.2))
  set B := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ L p.1 > L p.2)
  have h1 : (A.erase (i.val, nextPosition i)).card ≤ B.card := by
    refine Finset.card_le_card_of_injOn (fun p => (adjacentPerm i p.1, adjacentPerm i p.2)) ?_ ?_
    · intro p hp
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, A, Finset.mem_filter,
        Finset.mem_univ, true_and, Set.mem_singleton_iff] at hp
      simp only [Finset.mem_coe, B, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, hp.1.2⟩
      have := g65d_perm_lt i p.1 p.2 hp.1.1 (by
        rintro ⟨h1, h2⟩; exact hp.2 (Prod.ext h1 h2))
      exact this
    · intro p _ q _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext ((adjacentPerm i).injective h.1) ((adjacentPerm i).injective h.2)
  have h2 := Finset.pred_card_le_card_erase (s := A) (a := (i.val, nextPosition i))
  omega

theorem g65d_cnt_eq {n : ℕ} (L : Fin n → ℕ) (i : Adjacent n) (hinv : L i.val > L (nextPosition i)) :
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ L (adjacentPerm i p.1) > L (adjacentPerm i p.2))).card
      + 1 = (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ L p.1 > L p.2)).card := by
  set A := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ L (adjacentPerm i p.1) > L (adjacentPerm i p.2))
  set B := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ L p.1 > L p.2)
  have hs : ∀ a, adjacentPerm i (adjacentPerm i a) = a := fun a => by simp [adjacentPerm]
  have hnl : (i.val : Fin n) < nextPosition i := by
    rw [Fin.lt_def]; simp [nextPosition]
  have hxB : (i.val, nextPosition i) ∈ B := by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hnl, hinv⟩
  have hsi : adjacentPerm i i.val = nextPosition i := by simp [adjacentPerm]
  have hsn : adjacentPerm i (nextPosition i) = i.val := by simp [adjacentPerm]
  have hcard : A.card = (B.erase (i.val, nextPosition i)).card := by
    refine Finset.card_bij' (fun p _ => (adjacentPerm i p.1, adjacentPerm i p.2))
      (fun p _ => (adjacentPerm i p.1, adjacentPerm i p.2)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_erase, B, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
        Prod.mk.injEq]
      have hpx : ¬ (p.1 = i.val ∧ p.2 = nextPosition i) := by
        rintro ⟨h1, h2⟩; rw [h1, h2, hsi, hsn] at hp; omega
      refine ⟨?_, g65d_perm_lt i p.1 p.2 hp.1 hpx, hp.2⟩
      rintro ⟨h1, h2⟩
      have e1 : p.1 = nextPosition i := by rw [← hs p.1, h1, hsi]
      have e2 : p.2 = i.val := by rw [← hs p.2, h2, hsn]
      have := hp.1; rw [e1, e2] at this; exact absurd (this.trans hnl) (lt_irrefl _)
    · intro q hq
      simp only [Finset.mem_erase, B, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq] at hq
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, hs]
      refine ⟨g65d_perm_lt i q.1 q.2 hq.2.1 (by rintro ⟨h1, h2⟩; exact hq.1 (Prod.ext h1 h2)), hq.2.2⟩
    · intro p _; simp [hs]
    · intro q _; simp [hs]
  rw [hcard, Finset.card_erase_add_one hxB]

def g65d_Path {n : ℕ} (T U : YoungTableau n) (r : ℕ) : Prop :=
  ∃ chain : Fin (r + 1) → YoungTableau n, chain 0 = T ∧ chain (Fin.last r) = U ∧
    ∀ j : Fin r, TableauStep (chain j.castSucc) (chain j.succ)

theorem g65d_path_refl {n : ℕ} (T : YoungTableau n) : g65d_Path T T 0 :=
  ⟨fun _ => T, rfl, rfl, fun j => j.elim0⟩

theorem g65d_path_head {n r : ℕ} {T T1 U : YoungTableau n} (h : TableauStep T T1)
    (hp : g65d_Path T1 U r) : g65d_Path T U (r + 1) := by
  obtain ⟨c, h0, hl, hs⟩ := hp
  refine ⟨Fin.cons T c, by simp, ?_, ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ]; exact hl
  · intro j
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one]
      have : (Fin.cons T c : Fin (r + 2) → YoungTableau n) 1 = c 0 := Fin.cons_succ (α := fun _ => YoungTableau n) T c 0
      rw [this, h0]; exact h
    · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]; exact hs j'

theorem g65d_path_tail {n r : ℕ} {T U : YoungTableau n} (hp : g65d_Path T U (r + 1)) :
    ∃ T1, TableauStep T T1 ∧ g65d_Path T1 U r := by
  obtain ⟨c, h0, hl, hs⟩ := hp
  refine ⟨c 1, ?_, fun j => c j.succ, rfl, ?_, fun j => ?_⟩
  · have := hs 0; rw [Fin.castSucc_zero, h0] at this; simpa using this
  · show c (Fin.last r).succ = U
    rw [Fin.succ_last]; exact hl
  · have := hs j.succ; rw [← Fin.succ_castSucc] at this; exact this

theorem g65d_path_trans {n : ℕ} : ∀ r1 : ℕ, ∀ {T T' U : YoungTableau n} {r2 : ℕ},
    g65d_Path T T' r1 → g65d_Path T' U r2 → g65d_Path T U (r1 + r2) := by
  intro r1
  induction r1 with
  | zero =>
    intro T T' U r2 h1 h2
    obtain ⟨c, h0, hl, _⟩ := h1
    have : T = T' := by rw [← h0, ← hl]; rfl
    subst this; simpa using h2
  | succ r ih =>
    intro T T' U r2 h1 h2
    obtain ⟨T1, hs, hp⟩ := g65d_path_tail h1
    have := g65d_path_head hs (ih hp h2)
    rwa [show r + r2 + 1 = r + 1 + r2 by omega] at this

theorem g65d_move2 {n k : ℕ} (hk : k < n) (U : YoungTableau n) :
    ∀ d : ℕ, ∀ (T : YoungTableau n) (j : Fin n), j.val + d = k → T.val j = U.val ⟨k, hk⟩ →
      Finset.univ.image T.val = Finset.univ.image U.val →
      (∀ l : Fin n, k < l.val → T.val l = U.val l) →
      ∃ T' : YoungTableau n, ∃ r : ℕ, g65d_Path T T' r ∧ r + g65d_inv U T'.val = g65d_inv U T.val ∧
        T'.val ⟨k, hk⟩ = U.val ⟨k, hk⟩ ∧ Finset.univ.image T'.val = Finset.univ.image U.val ∧
        (∀ l : Fin n, k < l.val → T'.val l = U.val l) := by
  intro d
  induction d with
  | zero =>
    intro T j hj hTj him hag
    have : j = ⟨k, hk⟩ := Fin.ext (by simpa using hj)
    subst this
    exact ⟨T, 0, g65d_path_refl T, by simp, hTj, him, hag⟩
  | succ d ih =>
    intro T j hj hTj him hag
    let i : Adjacent n := ⟨j, by omega⟩
    have hnext : (nextPosition i).val = j.val + 1 := rfl
    have hmem : T.val (nextPosition i) ∈ Finset.univ.image U.val := by
      rw [← him]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    obtain ⟨l', -, hl'⟩ := Finset.mem_image.mp hmem
    have hl'k : l'.val ≤ k := by
      by_contra hc
      have h1 := hag l' (by omega)
      rw [hl'] at h1
      have := T.property.1 h1
      rw [this] at hc; omega
    have hl'ne : l'.val ≠ k := by
      intro he
      have h2 : l' = ⟨k, hk⟩ := Fin.ext he
      rw [h2, ← hTj] at hl'
      have := congrArg Fin.val (T.property.1 hl')
      rw [hnext] at this; omega
    have hnot : ¬ (T.val i.val ≤ T.val (nextPosition i)) := by
      intro hle
      change T.val j ≤ _ at hle
      rw [hTj, ← hl'] at hle
      have h1 := g65d_mono U _ _ hle
      simp at h1; omega
    set T1 := g65d_swap T i hnot with hT1
    have hT1v : T1.val = T.val ∘ adjacentPerm i := rfl
    have hT1n : T1.val (nextPosition i) = U.val ⟨k, hk⟩ := by
      rw [hT1v, Function.comp_apply, adjacentPerm, Equiv.swap_apply_right]; exact hTj
    have him1 : Finset.univ.image T1.val = Finset.univ.image U.val := by
      rw [← him]; ext b; simp only [Finset.mem_image, Finset.mem_univ, true_and, hT1v,
        Function.comp_apply]
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨_, rfl⟩
      · rintro ⟨a, rfl⟩; exact ⟨adjacentPerm i a, by simp [adjacentPerm]⟩
    have hag1 : ∀ l : Fin n, k < l.val → T1.val l = U.val l := by
      intro l hl
      rw [hT1v, Function.comp_apply, adjacentPerm, Equiv.swap_apply_of_ne_of_ne]
      · exact hag l hl
      · intro h; rw [h] at hl; change k < j.val at hl; omega
      · intro h; rw [h, hnext] at hl; omega
    have hcnt : g65d_inv U T1.val + 1 = g65d_inv U T.val := by
      refine g65d_cnt_eq (fun p => labelAt U (T.val p)) i ?_
      change labelAt U (T.val j) > labelAt U (T.val (nextPosition i))
      rw [hTj, ← hl', g65d_label_self, g65d_label_self]
      simp; omega
    obtain ⟨T', r, h1, hr, h2, h3, h4⟩ :=
      ih T1 (nextPosition i) (by rw [hnext]; omega) hT1n him1 hag1
    exact ⟨T', r + 1, g65d_path_head (g65d_step T i hnot) h1, by omega, h2, h3, h4⟩

theorem g65d_inv_self {n : ℕ} (U : YoungTableau n) : g65d_inv U U.val = 0 := by
  unfold g65d_inv
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ ⟨h1, h2⟩
  rw [g65d_label_self, g65d_label_self] at h2
  rw [Fin.lt_def] at h1; omega

theorem g65d_main2 {n : ℕ} : ∀ k : ℕ, ∀ T U : YoungTableau n,
    Finset.univ.image T.val = Finset.univ.image U.val →
    (∀ l : Fin n, k ≤ l.val → T.val l = U.val l) → g65d_Path T U (g65d_inv U T.val) := by
  intro k
  induction k with
  | zero =>
    intro T U _ hag
    have : T = U := Subtype.ext (funext fun l => hag l (Nat.zero_le _))
    subst this; rw [g65d_inv_self]; exact g65d_path_refl T
  | succ k ih =>
    intro T U him hag
    by_cases hk : k < n
    · have hmem : U.val ⟨k, hk⟩ ∈ Finset.univ.image T.val := by
        rw [him]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
      have hjk : j.val ≤ k := by
        by_contra hc
        have h1 := hag j (by omega)
        rw [hj] at h1
        have := congrArg Fin.val (U.property.1 h1)
        simp at this; omega
      obtain ⟨T', r, h1, hr, h2, h3, h4⟩ := g65d_move2 hk U (k - j.val) T j (by omega) hj him
        (fun l hl => hag l hl)
      have := g65d_path_trans r h1 (ih T' U h3 (fun l hl => ?_))
      · rwa [hr] at this
      rcases Nat.eq_or_lt_of_le hl with h | h
      · have : l = ⟨k, hk⟩ := Fin.ext h.symm
        rw [this]; exact h2
      · exact h4 l h
    · exact ih T U him (fun l hl => by omega)

theorem g65d_lower {n : ℕ} (U : YoungTableau n) : ∀ (word : List (Adjacent n)) (t : Fin n → ℕ × ℕ),
    U.val = t ∘ (word.map adjacentPerm).prod → g65d_inv U t ≤ word.length := by
  intro word
  induction word with
  | nil =>
    intro t ht
    simp only [List.map_nil, List.prod_nil, Equiv.Perm.coe_one, Function.comp_id] at ht
    subst ht; simp [g65d_inv_self]
  | cons a w ih =>
    intro t ht
    simp only [List.map_cons, List.prod_cons, Equiv.Perm.coe_mul] at ht
    have h1 := ih (t ∘ adjacentPerm a) (by rw [ht]; rfl)
    have hs : ∀ x, adjacentPerm a (adjacentPerm a x) = x := fun x => by simp [adjacentPerm]
    have h2 := g65d_cnt_le (fun p => labelAt U (t (adjacentPerm a p))) a
    simp only [hs] at h2
    change g65d_inv U t ≤ g65d_inv U (t ∘ adjacentPerm a) + 1 at h2
    simp only [List.length_cons]; omega

/-- Remark 5.6 (PDF p.21). Equal-shape tableaux admit an admissible path of
inversion length. The lower bound ranges over all adjacent-swapAlgebraElement words,
including words whose intermediate fillings fail to be tableaux. Different-shape
vectors need not share an orbit. -/
theorem solution {n : ℕ} (T U : YoungTableau n) (h : tableauShape T = tableauShape U) :
    (∃ r : ℕ, ∃ chain : Fin (r + 1) → YoungTableau n,
      chain 0 = T ∧ chain (Fin.last r) = U ∧
      (∀ j : Fin r, TableauStep (chain j.castSucc) (chain j.succ)) ∧
      r = inversionsBetween T U) ∧
    (∀ word : List (Adjacent n),
      U.val = T.val ∘ (word.map adjacentPerm).prod →
      inversionsBetween T U ≤ word.length) := by
  have him : Finset.univ.image T.val = Finset.univ.image U.val := congrArg YoungDiagram.cells h
  refine ⟨?_, fun word hw => g65d_lower U word T.val hw⟩
  obtain ⟨c, h0, hl, hs⟩ := g65d_main2 n T U him (fun l hl => by have := l.isLt; omega)
  exact ⟨_, c, h0, hl, hs, rfl⟩

end
