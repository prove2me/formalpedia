-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P28.gz_tableau_encoding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:07:54.91398+00:00
-- url     : https://prove2.me/submissions/debd3738-4931-43a7-9451-ce8dcc11f379

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P28
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P28

open scoped Matrix Kronecker ComplexConjugate

theorem g74l_natToBits_inj {m a b : ℕ} (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (h : QAlgorithms.natToBits m a = QAlgorithms.natToBits m b) : a = b := by
  unfold QAlgorithms.natToBits at h
  have := congrArg Fin.val ((QAlgorithms.bitsEquivFin m).symm.injective h)
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

theorem g74l_mono {n d : ℕ} (q : GZPattern n d) (c : Fin d) :
    ∀ k (r s : Fin d), s.val = r.val + k → (q.val r c).val ≤ (q.val s c).val := by
  intro k
  induction k with
  | zero => intro r s h; rw [show s = r from Fin.ext (by omega)]
  | succ k ih =>
    intro r s h
    let s' : Fin d := ⟨s.val - 1, by omega⟩
    have h1 := ih r s' (by simp [s']; omega)
    refine h1.trans ?_
    by_cases hc : c.val ≤ s'.val
    · exact (q.property.2.2.2 s' s c ⟨c.val + 1, by simp [s'] at hc; omega⟩
        (by simp [s']; omega) hc rfl).1
    · have := q.property.1 s' c (by omega)
      omega

theorem g74l_rowlt {n d : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (a : lambda.val.cells) : a.val.1 < d := by
  have hleft : (a.val.1, 0) ∈ lambda.val :=
    lambda.val.up_left_mem (by rfl) (Nat.zero_le _) a.property
  exact (YoungDiagram.mem_iff_lt_colLen.mp hleft).trans_le lambda.property.2

theorem g74l_K {n d : ℕ} (hd : 0 < d) (lambda : QAlgorithms.Schur.Partition d n)
    (q : GZPattern n d)
    (htop : ∀ c : Fin d, (q.val ⟨d - 1, by omega⟩ c).val = lambda.val.rowLen c.val)
    (a : lambda.val.cells) (r : Fin d) :
    gzTableau lambda hd q a ≤ r ↔
      a.val.2 < (q.val r ⟨a.val.1, g74l_rowlt lambda a⟩).val := by
  have hmem : a.val ∈ lambda.val := a.property
  have hlt : a.val.2 < (q.val ⟨d-1, by omega⟩ ⟨a.val.1, g74l_rowlt lambda a⟩).val := by
    rw [htop]
    have : (a.val.1, a.val.2) ∈ lambda.val := hmem
    exact YoungDiagram.mem_iff_lt_rowLen.mp this
  have hne : (Finset.univ.filter (fun r : Fin d =>
      a.val.2 < (q.val r ⟨a.val.1, g74l_rowlt lambda a⟩).val)).Nonempty :=
    ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩⟩
  dsimp only [gzTableau]
  rw [dif_pos hne]
  constructor
  · intro hle
    have hm := Finset.min'_mem _ hne
    rw [Finset.mem_filter] at hm
    have hle' := Fin.le_iff_val_le_val.mp hle
    exact lt_of_lt_of_le hm.2 (g74l_mono q _ (r.val - (Finset.min' _ hne).val) _ _ (by omega))
  · intro h
    exact Finset.min'_le _ r (Finset.mem_filter.mpr ⟨Finset.mem_univ r, h⟩)

theorem g74l_le_top {n d : ℕ} (hd : 0 < d) (lambda : QAlgorithms.Schur.Partition d n)
    (q : GZPattern n d)
    (htop : ∀ c : Fin d, (q.val ⟨d - 1, by omega⟩ c).val = lambda.val.rowLen c.val)
    (r c : Fin d) : (q.val r c).val ≤ lambda.val.rowLen c.val := by
  rw [← htop c]
  exact g74l_mono q c (d - 1 - r.val) r _ (by simp; omega)

theorem g74l_count_iff (L : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hdown : ∀ j j', j' ≤ j → P j → P j') (hL : ∀ j, P j → j < L) (j : ℕ) :
    j < ((Finset.range L).filter P).card ↔ P j := by
  constructor
  · intro hj
    by_contra hP
    have hsub : (Finset.range L).filter P ⊆ Finset.range j := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_range]
      by_contra hx'
      exact hP (hdown x j (by omega) hx.2)
    have := Finset.card_le_card hsub
    simp at this
    omega
  · intro hP
    have hsub : Finset.range (j + 1) ⊆ (Finset.range L).filter P := by
      intro x hx
      rw [Finset.mem_range] at hx
      have hPx := hdown j x (by omega) hP
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hL x hPx), hPx⟩
    have := Finset.card_le_card hsub
    simp at this
    omega

def g74l_P {n d : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (t : lambda.val.cells → Fin d) (r c j : ℕ) : Prop :=
  ∃ h : (c, j) ∈ lambda.val.cells, (t ⟨(c, j), h⟩).val ≤ r

open Classical in
def g74l_cnt {n d : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (t : lambda.val.cells → Fin d) (r c : ℕ) : ℕ :=
  ((Finset.range (lambda.val.rowLen c)).filter (g74l_P lambda t r c)).card

theorem g74l_cnt_iff {n d : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (t : lambda.val.cells → Fin d) (ht : QAlgorithms.Schur.IsSemistandardFilling lambda t)
    (r c j : ℕ) : j < g74l_cnt lambda t r c ↔ g74l_P lambda t r c j := by
  classical
  unfold g74l_cnt
  convert g74l_count_iff (lambda.val.rowLen c) (g74l_P lambda t r c) ?_ ?_ j
  · intro j j' hj ⟨h, hle⟩
    have h' : (c, j') ∈ lambda.val.cells :=
      lambda.val.up_left_mem (by rfl) hj h
    refine ⟨h', le_trans ?_ hle⟩
    rcases lt_or_eq_of_le hj with hlt | heq
    · exact Fin.le_iff_val_le_val.mp ((ht ⟨_, h'⟩ ⟨_, h⟩).1 rfl hlt)
    · subst heq; exact le_rfl
  · intro j ⟨h, _⟩
    exact YoungDiagram.mem_iff_lt_rowLen.mp h

theorem g74l_cnt_le {n d : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (t : lambda.val.cells → Fin d) (r c : ℕ) :
    g74l_cnt lambda t r c ≤ lambda.val.rowLen c := by
  classical
  unfold g74l_cnt
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem g74l_rowLen_le {n d : ℕ} (lambda : QAlgorithms.Schur.Partition d n) (c : ℕ) :
    lambda.val.rowLen c ≤ n := by
  rw [YoungDiagram.rowLen_eq_card]
  exact (Finset.card_filter_le _ _).trans_eq lambda.property.1

theorem g74l_sum_le {n d : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (t : lambda.val.cells → Fin d) (r : ℕ) :
    ∑ c : Fin d, g74l_cnt lambda t r c.val ≤ n := by
  classical
  unfold g74l_cnt
  rw [← Finset.card_sigma]
  refine le_trans ?_ lambda.property.1.le
  apply Finset.card_le_card_of_injOn (fun x => (x.1.val, x.2))
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter] at hx
    obtain ⟨h, _⟩ := hx.2.2
    exact h
  · intro x hx y hy hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    simp only at hxy
    have : x1 = y1 := Fin.ext hxy.1
    subst this
    simp [hxy.2]

theorem g74l_cnt_le_of {n d : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (t : lambda.val.cells → Fin d) (ht : QAlgorithms.Schur.IsSemistandardFilling lambda t)
    (r c r' c' : ℕ) (h : ∀ j, g74l_P lambda t r' c' j → g74l_P lambda t r c j) :
    g74l_cnt lambda t r' c' ≤ g74l_cnt lambda t r c := by
  by_contra hlt
  push_neg at hlt
  have h1 := (g74l_cnt_iff lambda t ht r' c' _).mp hlt
  have h2 := (g74l_cnt_iff lambda t ht r c _).mpr (h _ h1)
  omega

theorem g74l_ge {n d : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (t : lambda.val.cells → Fin d) (ht : QAlgorithms.Schur.IsSemistandardFilling lambda t) :
    ∀ i j (h : (i, j) ∈ lambda.val.cells), i ≤ (t ⟨(i, j), h⟩).val := by
  intro i
  induction i with
  | zero => intro j h; exact Nat.zero_le _
  | succ i ih =>
    intro j h
    have h' : (i, j) ∈ lambda.val.cells := lambda.val.up_left_mem (Nat.le_succ i) le_rfl h
    have h1 := ih j h'
    have h2 := Fin.lt_iff_val_lt_val.mp ((ht ⟨_, h'⟩ ⟨_, h⟩).2 rfl (Nat.lt_succ_self i))
    omega

theorem g74l_col {n d : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (t : lambda.val.cells → Fin d) (ht : QAlgorithms.Schur.IsSemistandardFilling lambda t)
    (a b j : ℕ) (hab : a ≤ b) (h : (b, j) ∈ lambda.val.cells) :
    ∃ h' : (a, j) ∈ lambda.val.cells, (t ⟨(a, j), h'⟩).val ≤ (t ⟨(b, j), h⟩).val := by
  have h' : (a, j) ∈ lambda.val.cells := lambda.val.up_left_mem hab le_rfl h
  refine ⟨h', ?_⟩
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact (Fin.lt_iff_val_lt_val.mp ((ht ⟨_, h'⟩ ⟨_, h⟩).2 rfl hlt)).le
  · subst heq; exact le_rfl

def g74l_qf {n d : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (t : lambda.val.cells → Fin d) : Fin d → Fin d → Fin (n + 1) :=
  fun r c => ⟨g74l_cnt lambda t r.val c.val, by
    have := g74l_cnt_le lambda t r.val c.val
    have := g74l_rowLen_le lambda c.val
    omega⟩

theorem g74l_isGZ {n d : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (t : lambda.val.cells → Fin d) (ht : QAlgorithms.Schur.IsSemistandardFilling lambda t) :
    IsGZPattern (g74l_qf lambda t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r c hrc
    show g74l_cnt lambda t r.val c.val = 0
    by_contra hne
    have := (g74l_cnt_iff lambda t ht r.val c.val 0).mp (by omega)
    obtain ⟨h, hle⟩ := this
    have := g74l_ge lambda t ht c.val 0 h
    omega
  · intro r a b hab
    show g74l_cnt lambda t r.val b.val ≤ g74l_cnt lambda t r.val a.val
    apply g74l_cnt_le_of lambda t ht
    intro j ⟨h, hle⟩
    obtain ⟨h', hle'⟩ := g74l_col lambda t ht a.val b.val j hab h
    exact ⟨h', hle'.trans hle⟩
  · intro r
    exact g74l_sum_le lambda t r.val
  · intro r s c e hs hc he
    constructor
    · show g74l_cnt lambda t r.val c.val ≤ g74l_cnt lambda t s.val c.val
      apply g74l_cnt_le_of lambda t ht
      intro j ⟨h, hle⟩
      exact ⟨h, by omega⟩
    · show g74l_cnt lambda t s.val e.val ≤ g74l_cnt lambda t r.val c.val
      apply g74l_cnt_le_of lambda t ht
      intro j ⟨h, hle⟩
      have h' : (c.val, j) ∈ lambda.val.cells :=
        lambda.val.up_left_mem (by omega) le_rfl h
      have h2 := Fin.lt_iff_val_lt_val.mp ((ht ⟨_, h'⟩ ⟨_, h⟩).2 rfl (show c.val < e.val by omega))
      exact ⟨h', by omega⟩

theorem g74l_det {n d : ℕ} (hd : 0 < d) (lambda : QAlgorithms.Schur.Partition d n)
    (q1 q2 : GZPattern n d)
    (htop1 : ∀ c : Fin d, (q1.val ⟨d - 1, by omega⟩ c).val = lambda.val.rowLen c.val)
    (htop2 : ∀ c : Fin d, (q2.val ⟨d - 1, by omega⟩ c).val = lambda.val.rowLen c.val)
    (heq : gzTableau lambda hd q1 = gzTableau lambda hd q2) : q1 = q2 := by
  apply Subtype.ext
  funext r c
  apply Fin.ext
  have b1 := g74l_le_top hd lambda q1 htop1 r c
  have b2 := g74l_le_top hd lambda q2 htop2 r c
  have key : ∀ j, j < lambda.val.rowLen c.val →
      (j < (q1.val r c).val ↔ j < (q2.val r c).val) := by
    intro j hj
    have hmem : (c.val, j) ∈ lambda.val.cells := YoungDiagram.mem_iff_lt_rowLen.mpr hj
    have k1 := g74l_K hd lambda q1 htop1 ⟨_, hmem⟩ r
    have k2 := g74l_K hd lambda q2 htop2 ⟨_, hmem⟩ r
    rw [heq] at k1
    exact k1.symm.trans k2
  rcases lt_trichotomy (q1.val r c).val (q2.val r c).val with h | h | h
  · have := (key _ (by omega)).mpr h; omega
  · exact h
  · have := (key _ (by omega)).mp h; omega

theorem solution (n d : ℕ) (hn : 1 ≤ n) (hd : 0 < d)
    (lambda : QAlgorithms.Schur.Partition d n) :
    (∀ q : GZPattern n d,
      (∀ c : Fin d, (q.val ⟨d - 1, by omega⟩ c).val = lambda.val.rowLen c.val) →
      QAlgorithms.Schur.IsSemistandardFilling lambda (gzTableau lambda hd q)) ∧
    (∀ t : lambda.val.cells → Fin d,
      QAlgorithms.Schur.IsSemistandardFilling lambda t →
      ∃! q : GZPattern n d,
        (∀ c : Fin d, (q.val ⟨d - 1, by omega⟩ c).val = lambda.val.rowLen c.val) ∧
        gzTableau lambda hd q = t) ∧
    Function.Injective (fun t : {t : lambda.val.cells → Fin d //
      QAlgorithms.Schur.IsSemistandardFilling lambda t} => tableauBinaryCode lambda t.val) ∧
    Fintype.card (lambda.val.cells × Fin (Nat.clog 2 d)) =
      n * Nat.clog 2 d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q htop a b
    constructor
    · intro h1 h2
      have kb := (g74l_K hd lambda q htop b (gzTableau lambda hd q b)).mp le_rfl
      apply (g74l_K hd lambda q htop a _).mpr
      have : (⟨a.val.1, g74l_rowlt lambda a⟩ : Fin d) = ⟨b.val.1, g74l_rowlt lambda b⟩ :=
        Fin.ext h1
      rw [this]
      omega
    · intro h1 h2
      set s := gzTableau lambda hd q b with hs
      have kb := (g74l_K hd lambda q htop b s).mp le_rfl
      have hsb : b.val.1 ≤ s.val := by
        by_contra hlt
        have := q.property.1 s ⟨b.val.1, g74l_rowlt lambda b⟩ (by simp; omega)
        omega
      have hb1 := g74l_rowlt lambda b
      let r : Fin d := ⟨s.val - 1, by omega⟩
      let c : Fin d := ⟨b.val.1 - 1, by omega⟩
      have hi := (q.property.2.2.2 r s c ⟨b.val.1, hb1⟩ (by simp [r]; omega)
        (by simp [r, c]; omega) (by simp [c]; omega)).2
      have hrow := q.property.2.1 r ⟨a.val.1, g74l_rowlt lambda a⟩ c (by simp [c]; omega)
      have ka := (g74l_K hd lambda q htop a r).mpr (by omega)
      rw [Fin.lt_iff_val_lt_val]
      rw [Fin.le_iff_val_le_val] at ka
      simp [r] at ka
      omega
  · intro t ht
    have htop : ∀ c : Fin d, ((⟨g74l_qf lambda t, g74l_isGZ lambda t ht⟩ : GZPattern n d).val
        ⟨d - 1, by omega⟩ c).val = lambda.val.rowLen c.val := by
      intro c
      show g74l_cnt lambda t (d - 1) c.val = lambda.val.rowLen c.val
      apply le_antisymm (g74l_cnt_le lambda t _ _)
      by_contra hlt
      push_neg at hlt
      have hmem : (c.val, g74l_cnt lambda t (d - 1) c.val) ∈ lambda.val.cells :=
        YoungDiagram.mem_iff_lt_rowLen.mpr hlt
      have := (g74l_cnt_iff lambda t ht (d - 1) c.val _).mpr
        ⟨hmem, by have := (t ⟨_, hmem⟩).isLt; omega⟩
      omega
    have hgz : gzTableau lambda hd ⟨g74l_qf lambda t, g74l_isGZ lambda t ht⟩ = t := by
      funext a
      have key : ∀ r : Fin d, gzTableau lambda hd ⟨g74l_qf lambda t, g74l_isGZ lambda t ht⟩ a ≤ r
          ↔ t a ≤ r := by
        intro r
        rw [g74l_K hd lambda _ htop a r]
        show a.val.2 < g74l_cnt lambda t r.val a.val.1 ↔ _
        rw [g74l_cnt_iff lambda t ht, Fin.le_iff_val_le_val]
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨a.property, h⟩⟩
      exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)
    refine ⟨⟨g74l_qf lambda t, g74l_isGZ lambda t ht⟩, ⟨htop, hgz⟩, ?_⟩
    intro q' ⟨htop', hgz'⟩
    exact g74l_det hd lambda q' _ htop' htop (hgz'.trans hgz.symm)
  · intro t1 t2 h
    apply Subtype.ext
    funext a
    apply Fin.ext
    have hlt : ∀ x : Fin d, x.val < 2 ^ Nat.clog 2 d := fun x =>
      lt_of_lt_of_le x.isLt (Nat.le_pow_clog (by norm_num) _)
    apply g74l_natToBits_inj (hlt _) (hlt _)
    funext b
    exact congrFun h (a, b)
  · simp [Fintype.card_prod, lambda.property.1]

end
