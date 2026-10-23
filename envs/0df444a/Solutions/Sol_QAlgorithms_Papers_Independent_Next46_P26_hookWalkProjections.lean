-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P26.hookWalkProjections
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:29:13.708263+00:00
-- url     : https://prove2.me/submissions/51daf529-69b5-4b30-a252-d64d5c6daf49

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

end QAlgorithms.Papers.Independent.Next46.P26

end

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Next46.P26 in
theorem solution (lam : YoungDiagram) (hne : lam.cells.Nonempty)
    (x y : ℕ → ℝ) (hpos : PositiveWeights lam x y)
    (I J : Finset ℕ) (i0 j0 r s : ℕ) (hc : (r, s) ∈ corners lam)
    (hi0 : i0 ∈ I) (hr : r ∈ I) (hI : ∀ i ∈ I, i0 ≤ i ∧ i ≤ r)
    (hj0 : j0 ∈ J) (hs : s ∈ J) (hJ : ∀ j ∈ J, j0 ≤ j ∧ j ≤ s) :
    projectionProb lam x y (i0, j0) I J =
      ((∏ i ∈ I.erase i0, x i) / (∏ i ∈ I.erase r, rowGap lam x y i r s)) *
      ((∏ j ∈ J.erase j0, y j) / (∏ j ∈ J.erase s, colGap lam x y j r s)) := by
  have hrs := (X7T_corner_facts hc).1
  have hfuel : (r - i0) + (s - j0) ≤ lam.card := by
    have := X7T_card lam r s hrs
    omega
  unfold projectionProb
  exact X7T_main lam x y hpos r s hc
    (fun I J p => if p.toFinset.image Prod.fst = I ∧ p.toFinset.image Prod.snd = J then 1 else 0)
    (fun I J p h => if_pos h) (fun I J p h => if_neg h)
    lam.card i0 j0 I J hi0 hr hI hj0 hs hJ hfuel

end
