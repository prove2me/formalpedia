-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P26.weightedHookWalk
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:29:15.918987+00:00
-- url     : https://prove2.me/submissions/cbc7eaab-9e52-4cbc-8434-098770da6e3c

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem X7T_succ_le {lam : YoungDiagram} {z t : Cell} (ht : t ∈ successors lam z) : z ≤ t := by
  simp only [successors, Finset.mem_filter] at ht
  rcases ht.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.le_def.mpr ⟨h2.le, h1.ge⟩
  · exact Prod.le_def.mpr ⟨h1.ge, h2.le⟩

theorem X7T_congr (lam : YoungDiagram) (x y : ℕ → ℝ) : ∀ (f : ℕ) (z : Cell) (e1 e2 : List Cell → ℝ),
    (∀ p : List Cell, (∀ c ∈ p, z ≤ c) → e1 (z :: p) = e2 (z :: p)) →
    walkEval (successors lam) x y f z e1 = walkEval (successors lam) x y f z e2 := by
  intro f
  induction f with
  | zero =>
    intro z e1 e2 h
    simp only [walkEval, h [] (by simp)]
  | succ f ih =>
    intro z e1 e2 h
    simp only [walkEval]
    split_ifs
    · exact h [] (by simp)
    · refine Finset.sum_congr rfl (fun t ht => ?_)
      congr 1
      apply ih
      intro p hp
      apply h (t :: p)
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact X7T_succ_le ht
      · exact le_trans (X7T_succ_le ht) (hp c hc)

theorem X7T_zero (lam : YoungDiagram) (x y : ℕ → ℝ) : ∀ (f : ℕ) (z : Cell) (e : List Cell → ℝ),
    (∀ p : List Cell, (∀ c ∈ p, z ≤ c) → e (z :: p) = 0) →
    walkEval (successors lam) x y f z e = 0 := by
  intro f
  induction f with
  | zero =>
    intro z e h
    simp only [walkEval, h [] (by simp)]
    split_ifs <;> rfl
  | succ f ih =>
    intro z e h
    simp only [walkEval]
    split_ifs
    · exact h [] (by simp)
    · apply Finset.sum_eq_zero
      intro t ht
      rw [ih t _ (fun p hp => h (t :: p) (by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact X7T_succ_le ht
        · exact le_trans (X7T_succ_le ht) (hp c hc))), mul_zero]

theorem X7T_succ_eq (lam : YoungDiagram) (i0 j0 : ℕ) :
    successors lam (i0, j0) =
      (Finset.Ico (i0 + 1) (lam.colLen j0)).image (fun k => (k, j0)) ∪
      (Finset.Ico (j0 + 1) (lam.rowLen i0)).image (fun l => (i0, l)) := by
  ext ⟨a, b⟩
  simp only [successors, Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_union,
    Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro ⟨hab, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · left
      subst h1
      exact ⟨a, ⟨h2, YoungDiagram.mem_iff_lt_colLen.mp hab⟩, rfl, rfl⟩
    · right
      subst h1
      exact ⟨b, ⟨h2, YoungDiagram.mem_iff_lt_rowLen.mp hab⟩, rfl, rfl⟩
  · rintro (⟨k, ⟨hk1, hk2⟩, rfl, rfl⟩ | ⟨l, ⟨hl1, hl2⟩, rfl, rfl⟩)
    · exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr hk2, Or.inl ⟨rfl, hk1⟩⟩
    · exact ⟨YoungDiagram.mem_iff_lt_rowLen.mpr hl2, Or.inr ⟨rfl, hl1⟩⟩

theorem X7T_denom (lam : YoungDiagram) (x y : ℕ → ℝ) (i0 j0 : ℕ) :
    ∑ u ∈ successors lam (i0, j0), moveWeight x y (i0, j0) u =
      (∑ k ∈ Finset.Ico (i0 + 1) (lam.colLen j0), x k) +
        ∑ l ∈ Finset.Ico (j0 + 1) (lam.rowLen i0), y l := by
  rw [X7T_succ_eq, Finset.sum_union, Finset.sum_image, Finset.sum_image]
  · congr 1
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [moveWeight]
    · refine Finset.sum_congr rfl (fun l hl => ?_)
      have : l ≠ j0 := by simp only [Finset.mem_Ico] at hl; omega
      simp [moveWeight, this]
  · intro a _ b _ h; simpa using h
  · intro a _ b _ h; simpa using h
  · rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq] at h1 h2
    obtain ⟨k, ⟨hk, _⟩, rfl, rfl⟩ := h1
    obtain ⟨l, ⟨hl, _⟩, h3, rfl⟩ := h2
    omega


theorem X7T_corner_facts {lam : YoungDiagram} {r s : ℕ} (hc : (r, s) ∈ corners lam) :
    (r, s) ∈ lam ∧ lam.colLen s = r + 1 ∧ lam.rowLen r = s + 1 := by
  simp only [corners, Finset.mem_filter, YoungDiagram.mem_cells] at hc
  obtain ⟨h0, h1, h2⟩ := hc
  refine ⟨h0, ?_, ?_⟩
  · have a := YoungDiagram.mem_iff_lt_colLen.mp h0
    have b : ¬ (r + 1 < lam.colLen s) := fun h => h1 (YoungDiagram.mem_iff_lt_colLen.mpr h)
    omega
  · have a := YoungDiagram.mem_iff_lt_rowLen.mp h0
    have b : ¬ (s + 1 < lam.rowLen r) := fun h => h2 (YoungDiagram.mem_iff_lt_rowLen.mpr h)
    omega

theorem X7T_main (lam : YoungDiagram) (x y : ℕ → ℝ) (hpos : PositiveWeights lam x y)
    (r s : ℕ) (hc : (r, s) ∈ corners lam)
    (ev : Finset ℕ → Finset ℕ → List Cell → ℝ)
    (hev1 : ∀ I J p, (p.toFinset.image Prod.fst = I ∧ p.toFinset.image Prod.snd = J) →
      ev I J p = 1)
    (hev0 : ∀ I J p, ¬ (p.toFinset.image Prod.fst = I ∧ p.toFinset.image Prod.snd = J) →
      ev I J p = 0) :
    ∀ (f i0 j0 : ℕ) (I J : Finset ℕ), i0 ∈ I → r ∈ I → (∀ i ∈ I, i0 ≤ i ∧ i ≤ r) →
      j0 ∈ J → s ∈ J → (∀ j ∈ J, j0 ≤ j ∧ j ≤ s) → (r - i0) + (s - j0) ≤ f →
      walkEval (successors lam) x y f (i0, j0) (ev I J) =
        ((∏ i ∈ I.erase i0, x i) / (∏ i ∈ I.erase r, rowGap lam x y i r s)) *
        ((∏ j ∈ J.erase j0, y j) / (∏ j ∈ J.erase s, colGap lam x y j r s)) := by
  obtain ⟨hrs, hcol, hrow⟩ := X7T_corner_facts hc
  obtain ⟨hx, hy⟩ := hpos
  have hr0 : r < lam.colLen 0 :=
    YoungDiagram.mem_iff_lt_colLen.mp (lam.up_left_mem le_rfl (Nat.zero_le s) hrs)
  have hs0 : s < lam.rowLen 0 :=
    YoungDiagram.mem_iff_lt_rowLen.mp (lam.up_left_mem (Nat.zero_le r) le_rfl hrs)
  have hxn : ∀ k, k < lam.colLen 0 → 0 ≤ x k := fun k hk => (hx k hk).le
  have hyn : ∀ l, l < lam.rowLen 0 → 0 ≤ y l := fun l hl => (hy l hl).le
  have hrg_nn : ∀ i, 0 ≤ rowGap lam x y i r s := by
    intro i
    unfold rowGap
    apply add_nonneg
    · apply Finset.sum_nonneg; intro k hk; simp only [Finset.mem_Ico] at hk
      exact hxn k (by omega)
    · apply Finset.sum_nonneg; intro l hl; simp only [Finset.mem_Ico] at hl
      have := lam.rowLen_anti 0 i (Nat.zero_le i)
      exact hyn l (by omega)
  have hcg_nn : ∀ j, 0 ≤ colGap lam x y j r s := by
    intro j
    unfold colGap
    apply add_nonneg
    · apply Finset.sum_nonneg; intro k hk; simp only [Finset.mem_Ico] at hk
      have := lam.colLen_anti 0 j (Nat.zero_le j)
      exact hxn k (by omega)
    · apply Finset.sum_nonneg; intro l hl; simp only [Finset.mem_Ico] at hl
      exact hyn l (by omega)
  have hrg_pos : ∀ i, i < r → 0 < rowGap lam x y i r s := by
    intro i hi
    unfold rowGap
    have h1 : x r ≤ ∑ k ∈ Finset.Ico (i + 1) (r + 1), x k :=
      Finset.single_le_sum (f := x) (fun k hk => by
        simp only [Finset.mem_Ico] at hk; exact hxn k (by omega))
        (by simp only [Finset.mem_Ico]; omega)
    have h2 : 0 ≤ ∑ l ∈ Finset.Ico (s + 1) (lam.rowLen i), y l := by
      apply Finset.sum_nonneg; intro l hl; simp only [Finset.mem_Ico] at hl
      have := lam.rowLen_anti 0 i (Nat.zero_le i)
      exact hyn l (by omega)
    have := hx r hr0
    linarith
  have hcg_pos : ∀ j, j < s → 0 < colGap lam x y j r s := by
    intro j hj
    unfold colGap
    have h1 : y s ≤ ∑ l ∈ Finset.Ico (j + 1) (s + 1), y l :=
      Finset.single_le_sum (f := y) (fun l hl => by
        simp only [Finset.mem_Ico] at hl; exact hyn l (by omega))
        (by simp only [Finset.mem_Ico]; omega)
    have h2 : 0 ≤ ∑ k ∈ Finset.Ico (r + 1) (lam.colLen j), x k := by
      apply Finset.sum_nonneg; intro k hk; simp only [Finset.mem_Ico] at hk
      have := lam.colLen_anti 0 j (Nat.zero_le j)
      exact hxn k (by omega)
    have := hy s hs0
    linarith
  have hrg_r : rowGap lam x y r r s = 0 := by simp [rowGap, hrow]
  have hcg_s : colGap lam x y s r s = 0 := by simp [colGap, hcol]
  have hsucc_rs : successors lam (r, s) = ∅ := by
    rw [X7T_succ_eq, hcol, hrow]; simp
  have hcorner : ∀ (f : ℕ) (I J : Finset ℕ), r ∈ I → (∀ i ∈ I, r ≤ i ∧ i ≤ r) →
      s ∈ J → (∀ j ∈ J, s ≤ j ∧ j ≤ s) →
      walkEval (successors lam) x y f (r, s) (ev I J) =
        ((∏ i ∈ I.erase r, x i) / (∏ i ∈ I.erase r, rowGap lam x y i r s)) *
        ((∏ j ∈ J.erase s, y j) / (∏ j ∈ J.erase s, colGap lam x y j r s)) := by
    intro f I J hrI hI hsJ hJ
    have hI1 : I = {r} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hrI, fun i hi => le_antisymm (hI i hi).2 (hI i hi).1⟩
    have hJ1 : J = {s} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hsJ, fun j hj => le_antisymm (hJ j hj).2 (hJ j hj).1⟩
    subst hI1 hJ1
    have hev : ev {r} {s} [(r, s)] = 1 := hev1 _ _ _ (by simp)
    cases f <;> simp [walkEval, hsucc_rs, hev]
  intro f
  induction f with
  | zero =>
    intro i0 j0 I J hi0 hrI hI hj0 hsJ hJ hf
    have e1 : i0 = r := by have := hI i0 hi0; omega
    have e2 : j0 = s := by have := hJ j0 hj0; omega
    subst e1 e2
    exact hcorner 0 I J hrI hI hsJ hJ
  | succ f ih =>
    intro i0 j0 I J hi0 hrI hI hj0 hsJ hJ hf
    by_cases hzc : i0 = r ∧ j0 = s
    · obtain ⟨rfl, rfl⟩ := hzc
      exact hcorner (f + 1) I J hrI hI hsJ hJ
    have hi0r : i0 ≤ r := (hI i0 hi0).2
    have hj0s : j0 ≤ s := (hJ j0 hj0).2
    set I' := I.erase i0 with hI'def
    set J' := J.erase j0 with hJ'def
    -- reduction of the events
    have hdown : ∀ k, i0 < k →
        walkEval (successors lam) x y f (k, j0) (fun tail => ev I J ((i0, j0) :: tail)) =
          walkEval (successors lam) x y f (k, j0) (ev I' J) := by
      intro k hk
      apply X7T_congr
      intro p hp
      have hiR : i0 ∉ (((k, j0) :: p).toFinset.image Prod.fst) := by
        intro h
        simp only [Finset.mem_image, List.mem_toFinset] at h
        obtain ⟨c, hc, hc1⟩ := h
        rcases List.mem_cons.mp hc with rfl | hc
        · simp at hc1; omega
        · have := (Prod.le_def.mp (hp c hc)).1; simp at this; omega
      have hjC : j0 ∈ (((k, j0) :: p).toFinset.image Prod.snd) := by
        simp only [Finset.mem_image, List.mem_toFinset]
        exact ⟨(k, j0), List.mem_cons_self .., rfl⟩
      have key : ((((i0, j0) :: (k, j0) :: p).toFinset.image Prod.fst = I ∧
          ((i0, j0) :: (k, j0) :: p).toFinset.image Prod.snd = J) ↔
          ((((k, j0) :: p).toFinset.image Prod.fst = I' ∧
            ((k, j0) :: p).toFinset.image Prod.snd = J))) := by
        rw [List.toFinset_cons (a := (i0, j0)), Finset.image_insert, Finset.image_insert,
          Finset.insert_eq_of_mem hjC]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          rw [hI'def, ← h1, Finset.erase_insert hiR]
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          rw [h1, hI'def, Finset.insert_erase hi0]
      by_cases h : (((k, j0) :: p).toFinset.image Prod.fst = I' ∧
            ((k, j0) :: p).toFinset.image Prod.snd = J)
      · rw [hev1 _ _ _ h, hev1 _ _ _ (key.mpr h)]
      · rw [hev0 _ _ _ h, hev0 _ _ _ (fun h' => h (key.mp h'))]
    have hright : ∀ l, j0 < l →
        walkEval (successors lam) x y f (i0, l) (fun tail => ev I J ((i0, j0) :: tail)) =
          walkEval (successors lam) x y f (i0, l) (ev I J') := by
      intro l hl
      apply X7T_congr
      intro p hp
      have hjC : j0 ∉ (((i0, l) :: p).toFinset.image Prod.snd) := by
        intro h
        simp only [Finset.mem_image, List.mem_toFinset] at h
        obtain ⟨c, hc, hc1⟩ := h
        rcases List.mem_cons.mp hc with rfl | hc
        · simp at hc1; omega
        · have := (Prod.le_def.mp (hp c hc)).2; simp at this; omega
      have hiR : i0 ∈ (((i0, l) :: p).toFinset.image Prod.fst) := by
        simp only [Finset.mem_image, List.mem_toFinset]
        exact ⟨(i0, l), List.mem_cons_self .., rfl⟩
      have key : ((((i0, j0) :: (i0, l) :: p).toFinset.image Prod.fst = I ∧
          ((i0, j0) :: (i0, l) :: p).toFinset.image Prod.snd = J) ↔
          ((((i0, l) :: p).toFinset.image Prod.fst = I ∧
            ((i0, l) :: p).toFinset.image Prod.snd = J'))) := by
        rw [List.toFinset_cons (a := (i0, j0)), Finset.image_insert, Finset.image_insert,
          Finset.insert_eq_of_mem hiR]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rw [hJ'def, ← h2, Finset.erase_insert hjC]
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rw [h2, hJ'def, Finset.insert_erase hj0]
      by_cases h : (((i0, l) :: p).toFinset.image Prod.fst = I ∧
            ((i0, l) :: p).toFinset.image Prod.snd = J')
      · rw [hev1 _ _ _ h, hev1 _ _ _ (key.mpr h)]
      · rw [hev0 _ _ _ h, hev0 _ _ _ (fun h' => h (key.mp h'))]
    have hdown0 : ∀ k, (∀ h : I'.Nonempty, k ≠ I'.min' h) →
        walkEval (successors lam) x y f (k, j0) (ev I' J) = 0 := by
      intro k hk
      apply X7T_zero
      intro p hp
      apply hev0
      rintro ⟨h1, -⟩
      have hkI : k ∈ I' := by
        rw [← h1]; simp only [Finset.mem_image, List.mem_toFinset]
        exact ⟨(k, j0), List.mem_cons_self .., rfl⟩
      have hne : I'.Nonempty := ⟨k, hkI⟩
      have hle := I'.min'_le k hkI
      have hm : I'.min' hne ∈ (((k, j0) :: p).toFinset.image Prod.fst) := by
        rw [h1]; exact I'.min'_mem hne
      simp only [Finset.mem_image, List.mem_toFinset] at hm
      obtain ⟨c, hc, hc1⟩ := hm
      have : k ≤ c.1 := by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact le_rfl
        · exact (Prod.le_def.mp (hp c hc)).1
      exact hk hne (le_antisymm (by rw [← hc1] at hle ⊢; omega) hle)
    have hright0 : ∀ l, (∀ h : J'.Nonempty, l ≠ J'.min' h) →
        walkEval (successors lam) x y f (i0, l) (ev I J') = 0 := by
      intro l hl
      apply X7T_zero
      intro p hp
      apply hev0
      rintro ⟨-, h1⟩
      have hlJ : l ∈ J' := by
        rw [← h1]; simp only [Finset.mem_image, List.mem_toFinset]
        exact ⟨(i0, l), List.mem_cons_self .., rfl⟩
      have hne : J'.Nonempty := ⟨l, hlJ⟩
      have hle := J'.min'_le l hlJ
      have hm : J'.min' hne ∈ (((i0, l) :: p).toFinset.image Prod.snd) := by
        rw [h1]; exact J'.min'_mem hne
      simp only [Finset.mem_image, List.mem_toFinset] at hm
      obtain ⟨c, hc, hc1⟩ := hm
      have : l ≤ c.2 := by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact le_rfl
        · exact (Prod.le_def.mp (hp c hc)).2
      exact hl hne (le_antisymm (by rw [← hc1] at hle ⊢; omega) hle)
    have hrI' : i0 < r → r ∈ I' := fun h => Finset.mem_erase.mpr ⟨by omega, hrI⟩
    have hI'r : I'.Nonempty → i0 < r := fun ⟨m, hm⟩ => by
      have h1 := Finset.mem_erase.mp hm; have := hI m h1.2; omega
    have hsJ' : j0 < s → s ∈ J' := fun h => Finset.mem_erase.mpr ⟨by omega, hsJ⟩
    have hJ's : J'.Nonempty → j0 < s := fun ⟨m, hm⟩ => by
      have h1 := Finset.mem_erase.mp hm; have := hJ m h1.2; omega
    set kk : ℕ := if h : I'.Nonempty then I'.min' h else i0 + 1 with hkk
    set ll : ℕ := if h : J'.Nonempty then J'.min' h else j0 + 1 with hll
    have hkk_spec : ∀ h : I'.Nonempty, kk = I'.min' h := fun h => by rw [hkk, dif_pos h]
    have hll_spec : ∀ h : J'.Nonempty, ll = J'.min' h := fun h => by rw [hll, dif_pos h]
    have hkk_I : ∀ h : I'.Nonempty, i0 < kk ∧ kk ≤ r := fun h => by
      rw [hkk_spec h]
      have hm := Finset.mem_erase.mp (I'.min'_mem h)
      have := hI _ hm.2
      omega
    have hll_J : ∀ h : J'.Nonempty, j0 < ll ∧ ll ≤ s := fun h => by
      rw [hll_spec h]
      have hm := Finset.mem_erase.mp (J'.min'_mem h)
      have := hJ _ hm.2
      omega
    have hkk_gt : i0 < kk := by
      by_cases h : I'.Nonempty
      · exact (hkk_I h).1
      · rw [hkk, dif_neg h]; omega
    have hll_gt : j0 < ll := by
      by_cases h : J'.Nonempty
      · exact (hll_J h).1
      · rw [hll, dif_neg h]; omega
    have hamem : I'.Nonempty → (kk, j0) ∈ successors lam (i0, j0) := fun h => by
      rw [X7T_succ_eq]
      apply Finset.mem_union_left
      rw [Finset.mem_image]
      refine ⟨kk, Finset.mem_Ico.mpr ⟨hkk_gt, ?_⟩, rfl⟩
      exact YoungDiagram.mem_iff_lt_colLen.mp (lam.up_left_mem (hkk_I h).2 hj0s hrs)
    have hbmem : J'.Nonempty → (i0, ll) ∈ successors lam (i0, j0) := fun h => by
      rw [X7T_succ_eq]
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨ll, Finset.mem_Ico.mpr ⟨hll_gt, ?_⟩, rfl⟩
      exact YoungDiagram.mem_iff_lt_rowLen.mp (lam.up_left_mem hi0r (hll_J h).2 hrs)
    have hne_succ : successors lam (i0, j0) ≠ ∅ := by
      by_cases h : i0 < r
      · exact Finset.ne_empty_of_mem (hamem ⟨r, hrI' h⟩)
      · have : j0 < s := by omega
        exact Finset.ne_empty_of_mem (hbmem ⟨s, hsJ' this⟩)
    -- nonvanishing of the products
    have hPr : ∀ K : Finset ℕ, (∀ i ∈ K, i < r) → ∏ i ∈ K, rowGap lam x y i r s ≠ 0 := by
      intro K hK
      exact Finset.prod_ne_zero_iff.mpr (fun i hi => (hrg_pos i (hK i hi)).ne')
    have hPc : ∀ K : Finset ℕ, (∀ j ∈ K, j < s) → ∏ j ∈ K, colGap lam x y j r s ≠ 0 := by
      intro K hK
      exact Finset.prod_ne_zero_iff.mpr (fun j hj => (hcg_pos j (hK j hj)).ne')
    have hIr : ∀ i ∈ I.erase r, i < r := fun i hi => by
      have h1 := Finset.mem_erase.mp hi; have := hI i h1.2; omega
    have hJs : ∀ j ∈ J.erase s, j < s := fun j hj => by
      have h1 := Finset.mem_erase.mp hj; have := hJ j h1.2; omega
    have hI'r' : ∀ i ∈ I'.erase r, i < r := fun i hi => by
      have h1 := Finset.mem_erase.mp hi
      exact hIr i (Finset.mem_erase.mpr ⟨h1.1, Finset.mem_of_mem_erase h1.2⟩)
    have hJ's' : ∀ j ∈ J'.erase s, j < s := fun j hj => by
      have h1 := Finset.mem_erase.mp hj
      exact hJs j (Finset.mem_erase.mpr ⟨h1.1, Finset.mem_of_mem_erase h1.2⟩)
    -- values at the two distinguished successors
    have hWa : moveWeight x y (i0, j0) (kk, j0) *
        walkEval (successors lam) x y f (kk, j0) (fun tail => ev I J ((i0, j0) :: tail)) =
        rowGap lam x y i0 r s *
          (((∏ i ∈ I.erase i0, x i) / (∏ i ∈ I.erase r, rowGap lam x y i r s)) *
          ((∏ j ∈ J.erase j0, y j) / (∏ j ∈ J.erase s, colGap lam x y j r s))) := by
      rw [hdown kk hkk_gt]
      by_cases h : I'.Nonempty
      · have hk := hkk_I h
        rw [hkk_spec h] at hk ⊢
        rw [ih (I'.min' h) j0 I' J (I'.min'_mem h) (hrI' (hI'r h))
          (fun i hi => ⟨I'.min'_le i hi, (hI i (Finset.mem_of_mem_erase hi)).2⟩) hj0 hsJ hJ
          (by omega)]
        have hmw : moveWeight x y (i0, j0) (I'.min' h, j0) = x (I'.min' h) := by
          simp [moveWeight]
        rw [hmw]
        have hi0Ir : i0 ∈ I.erase r := Finset.mem_erase.mpr ⟨by omega, hi0⟩
        rw [← Finset.mul_prod_erase I' x (I'.min'_mem h),
          ← Finset.mul_prod_erase (I.erase r) (fun i => rowGap lam x y i r s) hi0Ir,
          Finset.erase_right_comm (s := I) (a := r) (b := i0), ← hI'def]
        have h1 := hPr _ hI'r'
        have h2 := hPc _ hJs
        have h3 := (hrg_pos i0 (by omega)).ne'
        field_simp
      · rw [hdown0 kk (fun h' => absurd h' h), mul_zero]
        have : i0 = r := by
          by_contra hne; exact h ⟨r, hrI' (by omega)⟩
        rw [this, hrg_r, zero_mul]
    have hWb : moveWeight x y (i0, j0) (i0, ll) *
        walkEval (successors lam) x y f (i0, ll) (fun tail => ev I J ((i0, j0) :: tail)) =
        colGap lam x y j0 r s *
          (((∏ i ∈ I.erase i0, x i) / (∏ i ∈ I.erase r, rowGap lam x y i r s)) *
          ((∏ j ∈ J.erase j0, y j) / (∏ j ∈ J.erase s, colGap lam x y j r s))) := by
      rw [hright ll hll_gt]
      by_cases h : J'.Nonempty
      · have hl := hll_J h
        rw [hll_spec h] at hl ⊢
        rw [ih i0 (J'.min' h) I J' hi0 hrI hI (J'.min'_mem h) (hsJ' (hJ's h))
          (fun j hj => ⟨J'.min'_le j hj, (hJ j (Finset.mem_of_mem_erase hj)).2⟩)
          (by omega)]
        have hmw : moveWeight x y (i0, j0) (i0, J'.min' h) = y (J'.min' h) := by
          have : J'.min' h ≠ j0 := by omega
          simp [moveWeight, this]
        rw [hmw]
        have hj0Js : j0 ∈ J.erase s := Finset.mem_erase.mpr ⟨by omega, hj0⟩
        rw [← Finset.mul_prod_erase J' y (J'.min'_mem h),
          ← Finset.mul_prod_erase (J.erase s) (fun j => colGap lam x y j r s) hj0Js,
          Finset.erase_right_comm (s := J) (a := s) (b := j0), ← hJ'def]
        have h1 := hPc _ hJ's'
        have h2 := hPr _ hIr
        have h3 := (hcg_pos j0 (by omega)).ne'
        field_simp
      · rw [hright0 ll (fun h' => absurd h' h), mul_zero]
        have : j0 = s := by
          by_contra hne; exact h ⟨s, hsJ' (by omega)⟩
        rw [this, hcg_s, zero_mul]
    -- denominators
    have hH : (∑ k ∈ Finset.Ico (i0 + 1) (lam.colLen j0), x k) +
        ∑ l ∈ Finset.Ico (j0 + 1) (lam.rowLen i0), y l =
        rowGap lam x y i0 r s + colGap lam x y j0 r s := by
      have h1 : r + 1 ≤ lam.colLen j0 :=
        YoungDiagram.mem_iff_lt_colLen.mp (lam.up_left_mem le_rfl hj0s hrs)
      have h2 : s + 1 ≤ lam.rowLen i0 :=
        YoungDiagram.mem_iff_lt_rowLen.mp (lam.up_left_mem hi0r le_rfl hrs)
      unfold rowGap colGap
      rw [← Finset.sum_Ico_consecutive x (show i0 + 1 ≤ r + 1 by omega) h1,
        ← Finset.sum_Ico_consecutive y (show j0 + 1 ≤ s + 1 by omega) h2]
      ring
    have hHpos : 0 < rowGap lam x y i0 r s + colGap lam x y j0 r s := by
      by_cases h : i0 < r
      · have := hrg_pos i0 h; have := hcg_nn j0; linarith
      · have h' : j0 < s := by omega
        have := hcg_pos j0 h'; have := hrg_nn i0; linarith
    simp only [walkEval]
    rw [if_neg hne_succ, X7T_denom lam x y i0 j0, hH]
    simp only [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    have hab : (kk, j0) ≠ (i0, ll) := by
      intro h; simp only [Prod.mk.injEq] at h; omega
    rw [Finset.sum_eq_add (kk, j0) (i0, ll) hab]
    · rw [hWa, hWb, ← add_mul, mul_div_cancel_left₀ _ hHpos.ne']
      simp only [← hI'def, ← hJ'def]
      ring
    · intro c hc hne
      rw [X7T_succ_eq] at hc
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Ico] at hc
      rcases hc with ⟨k, ⟨hk1, hk2⟩, rfl⟩ | ⟨l, ⟨hl1, hl2⟩, rfl⟩
      · rw [hdown k (by omega), hdown0 k (fun h hk => hne.1 (by rw [hkk_spec h, hk])), mul_zero]
      · rw [hright l (by omega), hright0 l (fun h hl => hne.2 (by rw [hll_spec h, hl])),
          mul_zero]
    · intro hnot
      by_cases h : I'.Nonempty
      · exact absurd (hamem h) hnot
      · rw [hdown kk hkk_gt, hdown0 kk (fun h' => absurd h' h), mul_zero]
    · intro hnot
      by_cases h : J'.Nonempty
      · exact absurd (hbmem h) hnot
      · rw [hright ll hll_gt, hright0 ll (fun h' => absurd h' h), mul_zero]

theorem X7T_card (lam : YoungDiagram) (r s : ℕ) (hrs : (r, s) ∈ lam) :
    r + s ≤ lam.card := by
  have hsub : (Finset.range (r + 1) ×ˢ Finset.range (s + 1)) ⊆ lam.cells := by
    rintro ⟨a, b⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h
    rw [YoungDiagram.mem_cells]
    exact lam.up_left_mem (by omega) (by omega) hrs
  have := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_range, Finset.card_range] at this
  have : r + s ≤ (r + 1) * (s + 1) := by nlinarith
  unfold YoungDiagram.card
  omega


theorem X7T_congr2 (lam : YoungDiagram) (x y : ℕ → ℝ) : ∀ (f : ℕ) (z : Cell) (e1 e2 : List Cell → ℝ),
    (∀ p : List Cell, List.IsChain (· ≤ ·) (z :: p) → e1 (z :: p) = e2 (z :: p)) →
    walkEval (successors lam) x y f z e1 = walkEval (successors lam) x y f z e2 := by
  intro f
  induction f with
  | zero =>
    intro z e1 e2 h
    simp only [walkEval, h [] (by simp)]
  | succ f ih =>
    intro z e1 e2 h
    simp only [walkEval]
    split_ifs
    · exact h [] (by simp)
    · refine Finset.sum_congr rfl (fun t ht => ?_)
      congr 1
      apply ih
      intro p hp
      apply h (t :: p)
      exact List.isChain_cons_cons.mpr ⟨X7T_succ_le ht, hp⟩

theorem X7T_lin (lam : YoungDiagram) (x y : ℕ → ℝ) {ι : Type} (K : Finset ι) :
    ∀ (f : ℕ) (z : Cell) (e : ι → List Cell → ℝ),
    walkEval (successors lam) x y f z (fun p => ∑ k ∈ K, e k p) =
      ∑ k ∈ K, walkEval (successors lam) x y f z (e k) := by
  intro f
  induction f with
  | zero =>
    intro z e
    simp only [walkEval]
    split_ifs
    · rfl
    · simp
  | succ f ih =>
    intro z e
    simp only [walkEval]
    split_ifs
    · rfl
    · have h1 : ∀ t, walkEval (successors lam) x y f t
          (fun tail => ∑ k ∈ K, e k (z :: tail)) =
          ∑ k ∈ K, walkEval (successors lam) x y f t (fun tail => e k (z :: tail)) :=
        fun t => ih t (fun k tail => e k (z :: tail))
      simp only [h1, Finset.mul_sum]
      exact Finset.sum_comm

theorem X7T_chain_le_last : ∀ (z : Cell) (p : List Cell), List.IsChain (· ≤ ·) (z :: p) →
    ∀ a ∈ z :: p, z ≤ a ∧ a ≤ (z :: p).getLast (List.cons_ne_nil _ _) := by
  intro z p
  induction p generalizing z with
  | nil =>
    intro _ a ha
    simp only [List.mem_singleton] at ha
    subst ha
    simp
  | cons t p ih =>
    intro hc a ha
    have hzt := (List.isChain_cons_cons.mp hc).1
    have hrest := ih t (List.isChain_cons_cons.mp hc).2
    rw [List.getLast_cons (List.cons_ne_nil _ _)]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨le_rfl, le_trans hzt (hrest t (List.mem_cons_self ..)).2⟩
    · have := hrest a ha
      exact ⟨le_trans hzt this.1, this.2⟩

/-- the admissible row sets from i0 to r -/
def X7T_S (i0 r : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc i0 r).powerset.filter (fun I => i0 ∈ I ∧ r ∈ I)

theorem X7T_mem_S {i0 r : ℕ} {I : Finset ℕ} :
    I ∈ X7T_S i0 r ↔ i0 ∈ I ∧ r ∈ I ∧ ∀ i ∈ I, i0 ≤ i ∧ i ≤ r := by
  simp only [X7T_S, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h3, fun i hi => Finset.mem_Icc.mp (h1 hi)⟩
  · rintro ⟨h2, h3, h1⟩
    exact ⟨fun i hi => Finset.mem_Icc.mpr (h1 i hi), h2, h3⟩

theorem X7T_decomp (r s : ℕ) (z : Cell) (p : List Cell) (hc : List.IsChain (· ≤ ·) (z :: p)) :
    (if (z :: p).getLast? = some (r, s) then (1 : ℝ) else 0) =
      ∑ I ∈ X7T_S z.1 r, ∑ J ∈ X7T_S z.2 s,
        (if (z :: p).toFinset.image Prod.fst = I ∧ (z :: p).toFinset.image Prod.snd = J
          then (1 : ℝ) else 0) := by
  have hle := X7T_chain_le_last z p hc
  set L := (z :: p).getLast (List.cons_ne_nil _ _) with hLdef
  have hLmem : L ∈ z :: p := List.getLast_mem _
  rw [List.getLast?_eq_getLast (List.cons_ne_nil _ _)]
  by_cases hL : L = (r, s)
  · rw [if_pos (by rw [← hLdef, hL])]
    have hrows : (z :: p).toFinset.image Prod.fst ∈ X7T_S z.1 r := by
      rw [X7T_mem_S]
      refine ⟨Finset.mem_image.mpr ⟨z, by simp, rfl⟩,
        Finset.mem_image.mpr ⟨L, List.mem_toFinset.mpr hLmem, by rw [hL]⟩, ?_⟩
      intro i hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      have := hle a (List.mem_toFinset.mp ha)
      rw [hL] at this
      exact ⟨(Prod.le_def.mp this.1).1, (Prod.le_def.mp this.2).1⟩
    have hcols : (z :: p).toFinset.image Prod.snd ∈ X7T_S z.2 s := by
      rw [X7T_mem_S]
      refine ⟨Finset.mem_image.mpr ⟨z, by simp, rfl⟩,
        Finset.mem_image.mpr ⟨L, List.mem_toFinset.mpr hLmem, by rw [hL]⟩, ?_⟩
      intro i hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      have := hle a (List.mem_toFinset.mp ha)
      rw [hL] at this
      exact ⟨(Prod.le_def.mp this.1).2, (Prod.le_def.mp this.2).2⟩
    simp only [ite_and]
    rw [Finset.sum_eq_single ((z :: p).toFinset.image Prod.fst)]
    · simp only [eq_self_iff_true, if_true, ite_true]
      rw [Finset.sum_ite_eq, if_pos hcols]
    · intro I _ hI
      rw [Finset.sum_eq_zero]
      intro J _
      rw [if_neg (Ne.symm hI)]
    · intro h; exact absurd hrows h
  · rw [if_neg (by rw [← hLdef]; intro h; exact hL (Option.some_injective _ h))]
    symm
    apply Finset.sum_eq_zero
    intro I hI
    apply Finset.sum_eq_zero
    intro J hJ
    rw [if_neg]
    rintro ⟨h1, h2⟩
    rw [X7T_mem_S] at hI hJ
    apply hL
    have hL1 : L.1 ∈ I := by
      rw [← h1]; exact Finset.mem_image.mpr ⟨L, List.mem_toFinset.mpr hLmem, rfl⟩
    have hL2 : L.2 ∈ J := by
      rw [← h2]; exact Finset.mem_image.mpr ⟨L, List.mem_toFinset.mpr hLmem, rfl⟩
    have hr : r ∈ (z :: p).toFinset.image Prod.fst := by rw [h1]; exact hI.2.1
    have hs : s ∈ (z :: p).toFinset.image Prod.snd := by rw [h2]; exact hJ.2.1
    obtain ⟨a, ha, har⟩ := Finset.mem_image.mp hr
    obtain ⟨b, hb, hbs⟩ := Finset.mem_image.mp hs
    have ha' := (Prod.le_def.mp (hle a (List.mem_toFinset.mp ha)).2).1
    have hb' := (Prod.le_def.mp (hle b (List.mem_toFinset.mp hb)).2).2
    have h3 := (hI.2.2 _ hL1).2
    have h4 := (hJ.2.2 _ hL2).2
    ext
    · simp only; omega
    · simp only; omega

theorem X7T_rowsum (x g : ℕ → ℝ) (r : ℕ) (hg : ∀ i < r, g i ≠ 0) :
    ∑ i0 ∈ Finset.range (r + 1), x i0 *
      ∑ I ∈ X7T_S i0 r, (∏ i ∈ I.erase i0, x i) / (∏ i ∈ I.erase r, g i) =
    x r * ∏ i ∈ Finset.range r, (1 + x i / g i) := by
  have step1 : ∀ i0 ∈ Finset.range (r + 1), x i0 *
      ∑ I ∈ X7T_S i0 r, (∏ i ∈ I.erase i0, x i) / (∏ i ∈ I.erase r, g i) =
      ∑ I ∈ X7T_S i0 r, (∏ i ∈ I, x i) / (∏ i ∈ I.erase r, g i) := by
    intro i0 _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun I hI => ?_)
    rw [← Finset.mul_prod_erase I x (X7T_mem_S.mp hI).1, mul_div_assoc]
  rw [Finset.sum_congr rfl step1]
  have hdisj : (↑(Finset.range (r + 1)) : Set ℕ).PairwiseDisjoint (fun i0 => X7T_S i0 r) := by
    intro i hi j hj hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro I h1 h2
    rw [X7T_mem_S] at h1 h2
    have a := h1.2.2 j h2.1
    have b := h2.2.2 i h1.1
    exact hij (le_antisymm a.1 b.1)
  rw [← Finset.sum_biUnion hdisj]
  have hU : (Finset.range (r + 1)).biUnion (fun i0 => X7T_S i0 r) =
      (Finset.range (r + 1)).powerset.filter (fun I => r ∈ I) := by
    ext I
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset, Finset.mem_range]
    constructor
    · rintro ⟨i0, hi0, hI⟩
      rw [X7T_mem_S] at hI
      refine ⟨fun i hi => Finset.mem_range.mpr (by have := hI.2.2 i hi; omega), hI.2.1⟩
    · rintro ⟨hsub, hr⟩
      have hne : I.Nonempty := ⟨r, hr⟩
      refine ⟨I.min' hne, ?_, ?_⟩
      · have := Finset.mem_range.mp (hsub (I.min'_mem hne)); omega
      · rw [X7T_mem_S]
        refine ⟨I.min'_mem hne, hr, fun i hi => ⟨I.min'_le i hi, ?_⟩⟩
        have := Finset.mem_range.mp (hsub hi); omega
  rw [hU, Finset.sum_filter, Finset.range_add_one,
    Finset.sum_powerset_insert (Finset.notMem_range_self)]
  have h0 : ∑ t ∈ (Finset.range r).powerset,
      (if r ∈ t then (∏ i ∈ t, x i) / (∏ i ∈ t.erase r, g i) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    rw [if_neg]
    intro h
    exact Finset.notMem_range_self (Finset.mem_powerset.mp ht h)
  rw [h0, zero_add, Finset.prod_one_add, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have hrt : r ∉ t := fun h => Finset.notMem_range_self (Finset.mem_powerset.mp ht h)
  rw [if_pos (Finset.mem_insert_self _ _), Finset.prod_insert hrt, Finset.erase_insert hrt,
    Finset.prod_div_distrib, mul_div_assoc]

theorem X7T_S_empty {i0 r : ℕ} (h : r < i0) : X7T_S i0 r = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro I hI
  rw [X7T_mem_S] at hI
  have := hI.2.2 i0 hI.1
  omega

theorem X7T_gaps_pos (lam : YoungDiagram) (x y : ℕ → ℝ) (hpos : PositiveWeights lam x y)
    (r s : ℕ) (hc : (r, s) ∈ corners lam) :
    (∀ i, i < r → 0 < rowGap lam x y i r s) ∧ (∀ j, j < s → 0 < colGap lam x y j r s) := by
  obtain ⟨hrs, hcol, hrow⟩ := X7T_corner_facts hc
  obtain ⟨hx, hy⟩ := hpos
  have hr0 : r < lam.colLen 0 :=
    YoungDiagram.mem_iff_lt_colLen.mp (lam.up_left_mem le_rfl (Nat.zero_le s) hrs)
  have hs0 : s < lam.rowLen 0 :=
    YoungDiagram.mem_iff_lt_rowLen.mp (lam.up_left_mem (Nat.zero_le r) le_rfl hrs)
  have hxn : ∀ k, k < lam.colLen 0 → 0 ≤ x k := fun k hk => (hx k hk).le
  have hyn : ∀ l, l < lam.rowLen 0 → 0 ≤ y l := fun l hl => (hy l hl).le
  constructor
  · intro i hi
    unfold rowGap
    have h1 : x r ≤ ∑ k ∈ Finset.Ico (i + 1) (r + 1), x k :=
      Finset.single_le_sum (f := x) (fun k hk => by
        simp only [Finset.mem_Ico] at hk; exact hxn k (by omega))
        (by simp only [Finset.mem_Ico]; omega)
    have h2 : 0 ≤ ∑ l ∈ Finset.Ico (s + 1) (lam.rowLen i), y l := by
      apply Finset.sum_nonneg; intro l hl; simp only [Finset.mem_Ico] at hl
      have := lam.rowLen_anti 0 i (Nat.zero_le i)
      exact hyn l (by omega)
    have := hx r hr0
    linarith
  · intro j hj
    unfold colGap
    have h1 : y s ≤ ∑ l ∈ Finset.Ico (j + 1) (s + 1), y l :=
      Finset.single_le_sum (f := y) (fun l hl => by
        simp only [Finset.mem_Ico] at hl; exact hyn l (by omega))
        (by simp only [Finset.mem_Ico]; omega)
    have h2 : 0 ≤ ∑ k ∈ Finset.Ico (r + 1) (lam.colLen j), x k := by
      apply Finset.sum_nonneg; intro k hk; simp only [Finset.mem_Ico] at hk
      have := lam.colLen_anti 0 j (Nat.zero_le j)
      exact hxn k (by omega)
    have := hy s hs0
    linarith

end QAlgorithms.Papers.Independent.Next46.P26

end

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Next46.P26 in
theorem solution (lam : YoungDiagram) (hne : lam.cells.Nonempty)
    (x y : ℕ → ℝ) (hpos : PositiveWeights lam x y) (c : Cell) (hc : c ∈ corners lam) :
    terminalProb lam (successors lam) x y c =
      cornerWeight lam x y c.1 c.2 / totalWeight lam x y := by
  obtain ⟨r, s⟩ := c
  obtain ⟨hrs, hcol, hrow⟩ := X7T_corner_facts hc
  obtain ⟨hrg, hcg⟩ := X7T_gaps_pos lam x y hpos r s hc
  have hcard := X7T_card lam r s hrs
  set ev : Finset ℕ → Finset ℕ → List Cell → ℝ := fun I J p =>
    if p.toFinset.image Prod.fst = I ∧ p.toFinset.image Prod.snd = J then 1 else 0 with hev
  have hW : ∀ z ∈ lam.cells,
      walkEval (successors lam) x y lam.card z
        (fun p => if p.getLast? = some (r, s) then 1 else 0) =
      (∑ I ∈ X7T_S z.1 r, (∏ i ∈ I.erase z.1, x i) / (∏ i ∈ I.erase r, rowGap lam x y i r s)) *
      (∑ J ∈ X7T_S z.2 s, (∏ j ∈ J.erase z.2, y j) / (∏ j ∈ J.erase s, colGap lam x y j r s)) := by
    intro z _
    obtain ⟨i0, j0⟩ := z
    rw [X7T_congr2 lam x y _ (i0, j0) _ (fun p => ∑ I ∈ X7T_S i0 r, ∑ J ∈ X7T_S j0 s, ev I J p)
      (fun p hp => X7T_decomp r s (i0, j0) p hp)]
    have h1 := X7T_lin lam x y (X7T_S i0 r) lam.card (i0, j0)
      (fun I p => ∑ J ∈ X7T_S j0 s, ev I J p)
    rw [h1, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun I hI => ?_)
    have h2 := X7T_lin lam x y (X7T_S j0 s) lam.card (i0, j0) (fun J p => ev I J p)
    rw [h2]
    refine Finset.sum_congr rfl (fun J hJ => ?_)
    rw [X7T_mem_S] at hI hJ
    exact X7T_main lam x y hpos r s hc ev (fun I J p h => if_pos h) (fun I J p h => if_neg h)
      lam.card i0 j0 I J hI.1 hI.2.1 hI.2.2 hJ.1 hJ.2.1 hJ.2.2 (by omega)
  unfold terminalProb
  rw [Finset.sum_congr rfl (fun z hz => by rw [hW z hz])]
  set AR : ℕ → ℝ := fun i0 => ∑ I ∈ X7T_S i0 r,
    (∏ i ∈ I.erase i0, x i) / (∏ i ∈ I.erase r, rowGap lam x y i r s) with hAR
  set AC : ℕ → ℝ := fun j0 => ∑ J ∈ X7T_S j0 s,
    (∏ j ∈ J.erase j0, y j) / (∏ j ∈ J.erase s, colGap lam x y j r s) with hAC
  have hsub : (Finset.range (r + 1) ×ˢ Finset.range (s + 1)) ⊆ lam.cells := by
    rintro ⟨a, b⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h
    rw [YoungDiagram.mem_cells]
    exact lam.up_left_mem (by omega) (by omega) hrs
  have hR := X7T_rowsum x (fun i => rowGap lam x y i r s) r (fun i hi => (hrg i hi).ne')
  have hC := X7T_rowsum y (fun j => colGap lam x y j r s) s (fun j hj => (hcg j hj).ne')
  calc ∑ z ∈ lam.cells, x z.1 * y z.2 / totalWeight lam x y * (AR z.1 * AC z.2)
      = ∑ z ∈ Finset.range (r + 1) ×ˢ Finset.range (s + 1),
          x z.1 * y z.2 / totalWeight lam x y * (AR z.1 * AC z.2) := by
        symm
        apply Finset.sum_subset hsub
        intro z _ hz
        simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hz
        rcases hz with hz | hz
        · have : AR z.1 = 0 := by
            simp only [hAR]; rw [X7T_S_empty (by omega)]; simp
          rw [this]; ring
        · have : AC z.2 = 0 := by
            simp only [hAC]; rw [X7T_S_empty (by omega)]; simp
          rw [this]; ring
    _ = ∑ i0 ∈ Finset.range (r + 1), ∑ j0 ∈ Finset.range (s + 1),
          x i0 * y j0 / totalWeight lam x y * (AR i0 * AC j0) := Finset.sum_product _ _ _
    _ = (∑ i0 ∈ Finset.range (r + 1), x i0 * AR i0) *
          (∑ j0 ∈ Finset.range (s + 1), y j0 * AC j0) / totalWeight lam x y := by
        rw [Finset.sum_mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl (fun i0 _ => ?_)
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun j0 _ => ?_)
        ring
    _ = cornerWeight lam x y r s / totalWeight lam x y := by
        rw [hR, hC]
        unfold cornerWeight
        ring

end
