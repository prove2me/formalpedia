-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P26.modifiedHookWalk
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:59:19.541344+00:00
-- url     : https://prove2.me/submissions/e2720a43-e982-422a-88f6-ea55ad5a6a6f

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


theorem X7T_twalk (lam : YoungDiagram) (x y : ℕ → ℝ) (hpos : PositiveWeights lam x y)
    (r s : ℕ) (hc : (r, s) ∈ corners lam) (F : ℕ) (hF : r + s ≤ F) :
    ∑ z ∈ lam.cells, (x z.1 * y z.2 / totalWeight lam x y) *
      walkEval (successors lam) x y F z (fun p => if p.getLast? = some (r, s) then 1 else 0) =
      cornerWeight lam x y r s / totalWeight lam x y := by
  obtain ⟨hrs, hcol, hrow⟩ := X7T_corner_facts hc
  obtain ⟨hrg, hcg⟩ := X7T_gaps_pos lam x y hpos r s hc
  set ev : Finset ℕ → Finset ℕ → List Cell → ℝ := fun I J p =>
    if p.toFinset.image Prod.fst = I ∧ p.toFinset.image Prod.snd = J then 1 else 0 with hev
  have hW : ∀ z ∈ lam.cells,
      walkEval (successors lam) x y F z
        (fun p => if p.getLast? = some (r, s) then 1 else 0) =
      (∑ I ∈ X7T_S z.1 r, (∏ i ∈ I.erase z.1, x i) / (∏ i ∈ I.erase r, rowGap lam x y i r s)) *
      (∑ J ∈ X7T_S z.2 s, (∏ j ∈ J.erase z.2, y j) / (∏ j ∈ J.erase s, colGap lam x y j r s)) := by
    intro z _
    obtain ⟨i0, j0⟩ := z
    rw [X7T_congr2 lam x y _ (i0, j0) _ (fun p => ∑ I ∈ X7T_S i0 r, ∑ J ∈ X7T_S j0 s, ev I J p)
      (fun p hp => X7T_decomp r s (i0, j0) p hp)]
    have h1 := X7T_lin lam x y (X7T_S i0 r) F (i0, j0)
      (fun I p => ∑ J ∈ X7T_S j0 s, ev I J p)
    rw [h1, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun I hI => ?_)
    have h2 := X7T_lin lam x y (X7T_S j0 s) F (i0, j0) (fun J p => ev I J p)
    rw [h2]
    refine Finset.sum_congr rfl (fun J hJ => ?_)
    rw [X7T_mem_S] at hI hJ
    exact X7T_main lam x y hpos r s hc ev (fun I J p h => if_pos h) (fun I J p h => if_neg h)
      F i0 j0 I J hI.1 hI.2.1 hI.2.2 hJ.1 hJ.2.1 hJ.2.2 (by omega)
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


/-! ## Block structure for the modified walk -/

def X7M_rb (lam : YoungDiagram) (i : ℕ) : ℕ := ((corners lam).filter (fun c => c.1 < i)).card
def X7M_cb (lam : YoungDiagram) (j : ℕ) : ℕ := ((corners lam).filter (fun c => c.2 < j)).card

theorem X7M_cf {lam : YoungDiagram} {c : Cell} (hc : c ∈ corners lam) :
    c ∈ lam ∧ lam.colLen c.2 = c.1 + 1 ∧ lam.rowLen c.1 = c.2 + 1 := X7T_corner_facts hc

theorem X7M_inj1 {lam : YoungDiagram} {c c' : Cell} (hc : c ∈ corners lam) (hc' : c' ∈ corners lam)
    (h : c.1 = c'.1) : c = c' := by
  have a := (X7M_cf hc).2.2; have b := (X7M_cf hc').2.2
  rw [h] at a
  exact Prod.ext h (by omega)

theorem X7M_inj2 {lam : YoungDiagram} {c c' : Cell} (hc : c ∈ corners lam) (hc' : c' ∈ corners lam)
    (h : c.2 = c'.2) : c = c' := by
  have a := (X7M_cf hc).2.1; have b := (X7M_cf hc').2.1
  rw [h] at a
  exact Prod.ext (by omega) h

theorem X7M_above (lam : YoungDiagram) (z : Cell) (hz : z ∈ lam) :
    ∃ c ∈ corners lam, z ≤ c := by
  have hne : (lam.cells.filter (fun c => z ≤ c)).Nonempty :=
    ⟨z, Finset.mem_filter.mpr ⟨(YoungDiagram.mem_cells z).mpr hz, le_rfl⟩⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image _ (fun c : Cell => c.1 + c.2) hne
  rw [Finset.mem_filter, YoungDiagram.mem_cells] at hc
  refine ⟨c, ?_, hc.2⟩
  simp only [corners, Finset.mem_filter, YoungDiagram.mem_cells]
  refine ⟨hc.1, fun h => ?_, fun h => ?_⟩
  · have := hmax (c.1 + 1, c.2) (Finset.mem_filter.mpr ⟨(YoungDiagram.mem_cells _).mpr h,
      Prod.le_def.mpr ⟨by have := (Prod.le_def.mp hc.2).1; simp; omega,
        by have := (Prod.le_def.mp hc.2).2; simpa using this⟩⟩)
    simp at this
  · have := hmax (c.1, c.2 + 1) (Finset.mem_filter.mpr ⟨(YoungDiagram.mem_cells _).mpr h,
      Prod.le_def.mpr ⟨by have := (Prod.le_def.mp hc.2).1; simpa using this,
        by have := (Prod.le_def.mp hc.2).2; simp; omega⟩⟩)
    simp at this

theorem X7M_mem_iff (lam : YoungDiagram) (z : Cell) :
    z ∈ lam ↔ X7M_rb lam z.1 + X7M_cb lam z.2 + 1 ≤ (corners lam).card := by
  unfold X7M_rb X7M_cb
  set A := (corners lam).filter (fun c => c.1 < z.1)
  set B := (corners lam).filter (fun c => c.2 < z.2)
  constructor
  · intro hz
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro c hA hB
      rw [Finset.mem_filter] at hA hB
      have hcorner := hA.1
      simp only [corners, Finset.mem_filter] at hcorner
      apply hcorner.2.2
      exact lam.up_left_mem (by omega) (by omega) hz
    obtain ⟨c, hc, hzc⟩ := X7M_above lam z hz
    have hsub : A ∪ B ⊂ corners lam := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.union_subset (Finset.filter_subset _ _)
        (Finset.filter_subset _ _), fun h => ?_⟩
      have : c ∈ A ∪ B := by rw [h]; exact hc
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at this
      have h1 := Prod.le_def.mp hzc
      omega
    have := Finset.card_lt_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at this
    omega
  · intro h
    by_contra hz
    have hsub : corners lam ⊆ A ∪ B := by
      intro c hc
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_contra hn
      apply hz
      have hc1 := (X7M_cf hc).1
      have h1 : z.1 ≤ c.1 := by by_contra h'; exact hn (Or.inl ⟨hc, by omega⟩)
      have h2 : z.2 ≤ c.2 := by by_contra h'; exact hn (Or.inr ⟨hc, by omega⟩)
      exact lam.up_left_mem (i2 := c.1) (j2 := c.2) h1 h2 hc1
    have := Finset.card_le_card hsub
    have := Finset.card_union_le A B
    omega

theorem X7M_rb_mono (lam : YoungDiagram) {i i' : ℕ} (h : i ≤ i') : X7M_rb lam i ≤ X7M_rb lam i' :=
  Finset.card_le_card (Finset.monotone_filter_right _ (fun c _ (hc : c.1 < i) => by omega))

theorem X7M_cb_mono (lam : YoungDiagram) {j j' : ℕ} (h : j ≤ j') : X7M_cb lam j ≤ X7M_cb lam j' :=
  Finset.card_le_card (Finset.monotone_filter_right _ (fun c _ (hc : c.2 < j) => by omega))

theorem X7M_rb_lt_iff (lam : YoungDiagram) (i i' : ℕ) :
    X7M_rb lam i < X7M_rb lam i' ↔ ∃ c ∈ corners lam, i ≤ c.1 ∧ c.1 < i' := by
  unfold X7M_rb
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have : (corners lam).filter (fun c => c.1 < i') ⊆ (corners lam).filter (fun c => c.1 < i) := by
      intro c hc
      rw [Finset.mem_filter] at hc ⊢
      refine ⟨hc.1, ?_⟩
      by_contra h'
      exact absurd hc.2 (not_lt.mpr (hn c hc.1 (by omega)))
    have := Finset.card_le_card this
    omega
  · rintro ⟨c, hc, h1, h2⟩
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨fun d hd => ?_, fun h => ?_⟩
    · rw [Finset.mem_filter] at hd ⊢; exact ⟨hd.1, by omega⟩
    · have : c ∈ (corners lam).filter (fun c => c.1 < i') := Finset.mem_filter.mpr ⟨hc, h2⟩
      rw [← h, Finset.mem_filter] at this
      omega

theorem X7M_cb_lt_iff (lam : YoungDiagram) (j j' : ℕ) :
    X7M_cb lam j < X7M_cb lam j' ↔ ∃ c ∈ corners lam, j ≤ c.2 ∧ c.2 < j' := by
  unfold X7M_cb
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have : (corners lam).filter (fun c => c.2 < j') ⊆ (corners lam).filter (fun c => c.2 < j) := by
      intro c hc
      rw [Finset.mem_filter] at hc ⊢
      refine ⟨hc.1, ?_⟩
      by_contra h'
      exact absurd hc.2 (not_lt.mpr (hn c hc.1 (by omega)))
    have := Finset.card_le_card this
    omega
  · rintro ⟨c, hc, h1, h2⟩
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨fun d hd => ?_, fun h => ?_⟩
    · rw [Finset.mem_filter] at hd ⊢; exact ⟨hd.1, by omega⟩
    · have : c ∈ (corners lam).filter (fun c => c.2 < j') := Finset.mem_filter.mpr ⟨hc, h2⟩
      rw [← h, Finset.mem_filter] at this
      omega

theorem X7M_rb_corner_lt (lam : YoungDiagram) {c : Cell} (hc : c ∈ corners lam) :
    X7M_rb lam c.1 < (corners lam).card := by
  have := (X7M_mem_iff lam c).mp (X7M_cf hc).1; omega

theorem X7M_cb_corner_lt (lam : YoungDiagram) {c : Cell} (hc : c ∈ corners lam) :
    X7M_cb lam c.2 < (corners lam).card := by
  have := (X7M_mem_iff lam c).mp (X7M_cf hc).1; omega

theorem X7M_rb_surj (lam : YoungDiagram) (k : ℕ) (hk : k < (corners lam).card) :
    ∃ c ∈ corners lam, X7M_rb lam c.1 = k := by
  have := Finset.surjOn_of_injOn_of_card_le (s := corners lam) (t := Finset.range (corners lam).card)
    (fun c => X7M_rb lam c.1)
    (fun c hc => Finset.mem_range.mpr (X7M_rb_corner_lt lam hc))
    (by
      intro c hc c' hc' h
      simp only at h
      apply X7M_inj1 hc hc'
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h1 | h1
      · have := (X7M_rb_lt_iff lam c.1 c'.1).mpr ⟨c, hc, le_rfl, h1⟩; omega
      · have := (X7M_rb_lt_iff lam c'.1 c.1).mpr ⟨c', hc', le_rfl, h1⟩; omega)
    (by simp)
  obtain ⟨c, hc, h⟩ := this (Finset.mem_range.mpr hk)
  exact ⟨c, hc, h⟩

theorem X7M_cb_surj (lam : YoungDiagram) (k : ℕ) (hk : k < (corners lam).card) :
    ∃ c ∈ corners lam, X7M_cb lam c.2 = k := by
  have := Finset.surjOn_of_injOn_of_card_le (s := corners lam) (t := Finset.range (corners lam).card)
    (fun c => X7M_cb lam c.2)
    (fun c hc => Finset.mem_range.mpr (X7M_cb_corner_lt lam hc))
    (by
      intro c hc c' hc' h
      simp only at h
      apply X7M_inj2 hc hc'
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h1 | h1
      · have := (X7M_cb_lt_iff lam c.2 c'.2).mpr ⟨c, hc, le_rfl, h1⟩; omega
      · have := (X7M_cb_lt_iff lam c'.2 c.2).mpr ⟨c', hc', le_rfl, h1⟩; omega)
    (by simp)
  obtain ⟨c, hc, h⟩ := this (Finset.mem_range.mpr hk)
  exact ⟨c, hc, h⟩

theorem X7M_cb_zero (lam : YoungDiagram) : X7M_cb lam 0 = 0 := by simp [X7M_cb]
theorem X7M_rb_zero (lam : YoungDiagram) : X7M_rb lam 0 = 0 := by simp [X7M_rb]

theorem X7M_row_iff (lam : YoungDiagram) (i : ℕ) :
    i < lam.colLen 0 ↔ X7M_rb lam i < (corners lam).card := by
  rw [← YoungDiagram.mem_iff_lt_colLen, X7M_mem_iff]
  simp [X7M_cb_zero]

theorem X7M_col_iff (lam : YoungDiagram) (j : ℕ) :
    j < lam.rowLen 0 ↔ X7M_cb lam j < (corners lam).card := by
  rw [← YoungDiagram.mem_iff_lt_rowLen, X7M_mem_iff]
  simp [X7M_rb_zero]

/-- the staircase -/
def X7M_stair (m : ℕ) : YoungDiagram where
  cells := ((Finset.range m) ×ˢ (Finset.range m)).filter (fun u => u.1 + u.2 + 1 ≤ m)
  isLowerSet := by
    intro a b hab hb
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq] at hb ⊢
    have := Prod.le_def.mp hab
    omega

theorem X7M_stair_mem (m : ℕ) (u : Cell) : u ∈ X7M_stair m ↔ u.1 + u.2 + 1 ≤ m := by
  rw [← YoungDiagram.mem_cells]
  simp only [X7M_stair, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

theorem X7M_eq_of_lt_iff {a b : ℕ} (h : ∀ j, j < a ↔ j < b) : a = b := by
  have h1 := h a; have h2 := h b; omega

theorem X7M_stair_rowLen (m i : ℕ) : (X7M_stair m).rowLen i = m - i := by
  apply X7M_eq_of_lt_iff; intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, X7M_stair_mem]; omega

theorem X7M_stair_colLen (m j : ℕ) : (X7M_stair m).colLen j = m - j := by
  apply X7M_eq_of_lt_iff; intro i
  rw [← YoungDiagram.mem_iff_lt_colLen, X7M_stair_mem]; omega

theorem X7M_stair_corner (m r : ℕ) (hr : r < m) : (r, m - 1 - r) ∈ corners (X7M_stair m) := by
  simp only [corners, Finset.mem_filter, YoungDiagram.mem_cells, X7M_stair_mem]
  omega

theorem X7M_min_lt {s : Finset ℕ} {a : ℕ} : s.min < (a : WithTop ℕ) ↔ ∃ b ∈ s, b < a := by
  constructor
  · intro h
    cases hm : s.min with
    | top => rw [hm] at h; exact absurd h (not_lt.mpr le_top)
    | coe b =>
      rw [hm] at h
      exact ⟨b, Finset.mem_of_min hm, WithTop.coe_lt_coe.mp h⟩
  · rintro ⟨b, hb, hba⟩
    exact lt_of_le_of_lt (Finset.min_le hb) (WithTop.coe_lt_coe.mpr hba)

theorem X7M_msucc_iff (lam : YoungDiagram) (z t : Cell) :
    t ∈ modifiedSuccessors lam z ↔ t ∈ lam ∧
      ((t.2 = z.2 ∧ X7M_rb lam z.1 < X7M_rb lam t.1) ∨
       (t.1 = z.1 ∧ X7M_cb lam z.2 < X7M_cb lam t.2)) := by
  simp only [modifiedSuccessors, Finset.mem_filter, YoungDiagram.mem_cells, X7M_min_lt,
    Finset.mem_image, X7M_rb_lt_iff, X7M_cb_lt_iff]
  constructor
  · rintro ⟨h0, (⟨h1, b, ⟨c, hc, rfl⟩, h2⟩ | ⟨h1, b, ⟨c, hc, rfl⟩, h2⟩)⟩
    · exact ⟨h0, Or.inl ⟨h1, c, hc.1, hc.2, h2⟩⟩
    · exact ⟨h0, Or.inr ⟨h1, c, hc.1, hc.2, h2⟩⟩
  · rintro ⟨h0, (⟨h1, c, hc, h2, h3⟩ | ⟨h1, c, hc, h2, h3⟩)⟩
    · exact ⟨h0, Or.inl ⟨h1, c.1, ⟨c, ⟨hc, h2⟩, rfl⟩, h3⟩⟩
    · exact ⟨h0, Or.inr ⟨h1, c.2, ⟨c, ⟨hc, h2⟩, rfl⟩, h3⟩⟩

def X7M_pi (lam : YoungDiagram) (z : Cell) : Cell := (X7M_rb lam z.1, X7M_cb lam z.2)

def X7M_X (lam : YoungDiagram) (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ (Finset.range (lam.colLen 0)).filter (fun i => X7M_rb lam i = k), x i

def X7M_Y (lam : YoungDiagram) (y : ℕ → ℝ) (l : ℕ) : ℝ :=
  ∑ j ∈ (Finset.range (lam.rowLen 0)).filter (fun j => X7M_cb lam j = l), y j

theorem X7M_pi_mem (lam : YoungDiagram) {z : Cell} (hz : z ∈ lam) :
    X7M_pi lam z ∈ X7M_stair (corners lam).card := by
  rw [X7M_stair_mem]; exact (X7M_mem_iff lam z).mp hz

theorem X7M_mapsto (lam : YoungDiagram) {z t : Cell} (ht : t ∈ modifiedSuccessors lam z) :
    X7M_pi lam t ∈ successors (X7M_stair (corners lam).card) (X7M_pi lam z) := by
  rw [X7M_msucc_iff] at ht
  unfold successors
  rw [Finset.mem_filter, YoungDiagram.mem_cells]
  simp only [X7M_pi]
  refine ⟨X7M_pi_mem lam ht.1, ?_⟩
  rcases ht.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; rw [h1]; exact ⟨rfl, h2⟩
  · right; rw [h1]; exact ⟨rfl, h2⟩

theorem X7M_fiber (lam : YoungDiagram) (x y : ℕ → ℝ) {z : Cell} (hz : z ∈ lam) {v : Cell}
    (hv : v ∈ successors (X7M_stair (corners lam).card) (X7M_pi lam z)) :
    ∑ t ∈ (modifiedSuccessors lam z).filter (fun t => X7M_pi lam t = v), moveWeight x y z t =
      moveWeight (X7M_X lam x) (X7M_Y lam y) (X7M_pi lam z) v := by
  unfold successors at hv
  rw [Finset.mem_filter, YoungDiagram.mem_cells, X7M_stair_mem] at hv
  simp only [X7M_pi] at hv
  obtain ⟨hvm, hv⟩ := hv
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hset : (modifiedSuccessors lam z).filter (fun t => X7M_pi lam t = v) =
        ((Finset.range (lam.colLen 0)).filter (fun i => X7M_rb lam i = v.1)).image
          (fun i => (i, z.2)) := by
      ext t
      rw [Finset.mem_filter, X7M_msucc_iff, Finset.mem_image]
      simp only [Finset.mem_filter, Finset.mem_range, X7M_pi]
      constructor
      · rintro ⟨⟨ht0, (⟨ht1, ht2⟩ | ⟨ht1, ht2⟩)⟩, htv⟩
        · refine ⟨t.1, ⟨?_, by rw [← htv]⟩, by rw [← ht1]⟩
          rw [X7M_row_iff, show X7M_rb lam t.1 = v.1 by rw [← htv]]; omega
        · exfalso
          have : X7M_rb lam t.1 = v.1 := by rw [← htv]
          rw [ht1] at this; omega
      · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
        refine ⟨⟨?_, Or.inl ⟨rfl, by show X7M_rb lam z.1 < X7M_rb lam i; omega⟩⟩, ?_⟩
        · rw [X7M_mem_iff]; simp only; rw [hi2, ← h1]; omega
        · rw [hi2, ← h1]
    rw [hset, Finset.sum_image (fun a _ b _ h => by simpa using h)]
    simp only [moveWeight, if_true]
    have hpz : (X7M_pi lam z).2 = X7M_cb lam z.2 := rfl
    rw [h1, hpz, if_pos rfl]
    rfl
  · have hset : (modifiedSuccessors lam z).filter (fun t => X7M_pi lam t = v) =
        ((Finset.range (lam.rowLen 0)).filter (fun j => X7M_cb lam j = v.2)).image
          (fun j => (z.1, j)) := by
      ext t
      rw [Finset.mem_filter, X7M_msucc_iff, Finset.mem_image]
      simp only [Finset.mem_filter, Finset.mem_range, X7M_pi]
      constructor
      · rintro ⟨⟨ht0, (⟨ht1, ht2⟩ | ⟨ht1, ht2⟩)⟩, htv⟩
        · exfalso
          have : X7M_cb lam t.2 = v.2 := by rw [← htv]
          rw [ht1] at this; omega
        · refine ⟨t.2, ⟨?_, by rw [← htv]⟩, by rw [← ht1]⟩
          rw [X7M_col_iff, show X7M_cb lam t.2 = v.2 by rw [← htv]]; omega
      · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
        refine ⟨⟨?_, Or.inr ⟨rfl, by show X7M_cb lam z.2 < X7M_cb lam j; omega⟩⟩, ?_⟩
        · rw [X7M_mem_iff]; simp only; rw [hj2, ← h1]; omega
        · rw [hj2, ← h1]
    rw [hset, Finset.sum_image (fun a _ b _ h => by simpa using h)]
    have hv2 : v.2 ≠ X7M_cb lam z.2 := by omega
    simp only [moveWeight]
    rw [if_neg (show ¬ (v.2 = (X7M_pi lam z).2) from hv2)]
    unfold X7M_Y
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_filter] at hj
    have : j ≠ z.2 := by intro h; rw [h] at hj; omega
    simp [this]

theorem X7M_X_pos (lam : YoungDiagram) (x : ℕ → ℝ) (hx : ∀ i < lam.colLen 0, 0 < x i)
    (k : ℕ) (hk : k < (corners lam).card) : 0 < X7M_X lam x k := by
  obtain ⟨c, hc, hck⟩ := X7M_rb_surj lam k hk
  have hc0 : c.1 < lam.colLen 0 := (X7M_row_iff lam c.1).mpr (by omega)
  unfold X7M_X
  have hmem : c.1 ∈ (Finset.range (lam.colLen 0)).filter (fun i => X7M_rb lam i = k) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc0, hck⟩
  have := Finset.single_le_sum (f := x) (fun i hi => (hx i (Finset.mem_range.mp
    (Finset.mem_filter.mp hi).1)).le) hmem
  have := hx c.1 hc0
  linarith

theorem X7M_Y_pos (lam : YoungDiagram) (y : ℕ → ℝ) (hy : ∀ j < lam.rowLen 0, 0 < y j)
    (l : ℕ) (hl : l < (corners lam).card) : 0 < X7M_Y lam y l := by
  obtain ⟨c, hc, hcl⟩ := X7M_cb_surj lam l hl
  have hc0 : c.2 < lam.rowLen 0 := (X7M_col_iff lam c.2).mpr (by omega)
  unfold X7M_Y
  have hmem : c.2 ∈ (Finset.range (lam.rowLen 0)).filter (fun j => X7M_cb lam j = l) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc0, hcl⟩
  have := Finset.single_le_sum (f := y) (fun j hj => (hy j (Finset.mem_range.mp
    (Finset.mem_filter.mp hj).1)).le) hmem
  have := hy c.2 hc0
  linarith

theorem X7M_mw_pos (lam : YoungDiagram) (x y : ℕ → ℝ) (hx : ∀ i < lam.colLen 0, 0 < x i)
    (hy : ∀ j < lam.rowLen 0, 0 < y j) (u v : Cell)
    (hv : v ∈ X7M_stair (corners lam).card) :
    0 < moveWeight (X7M_X lam x) (X7M_Y lam y) u v := by
  rw [X7M_stair_mem] at hv
  unfold moveWeight
  split_ifs
  · exact X7M_X_pos lam x hx _ (by omega)
  · exact X7M_Y_pos lam y hy _ (by omega)

theorem X7M_transfer (lam : YoungDiagram) (x y : ℕ → ℝ) (hx : ∀ i < lam.colLen 0, 0 < x i)
    (hy : ∀ j < lam.rowLen 0, 0 < y j) : ∀ (f : ℕ) (z : Cell) (e : List Cell → ℝ), z ∈ lam →
    walkEval (modifiedSuccessors lam) x y f z (fun p => e (p.map (X7M_pi lam))) =
    walkEval (successors (X7M_stair (corners lam).card)) (X7M_X lam x) (X7M_Y lam y) f
      (X7M_pi lam z) e := by
  have hemp : ∀ z ∈ lam, (modifiedSuccessors lam z = ∅ ↔
      successors (X7M_stair (corners lam).card) (X7M_pi lam z) = ∅) := by
    intro z hz
    constructor
    · intro h
      by_contra hne
      obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have h1 := X7M_fiber lam x y hz hv
      have hvμ : v ∈ X7M_stair (corners lam).card := by
        unfold successors at hv
        exact (YoungDiagram.mem_cells _).mp (Finset.mem_filter.mp hv).1
      have h2 := X7M_mw_pos lam x y hx hy (X7M_pi lam z) v hvμ
      rw [h, Finset.filter_empty, Finset.sum_empty] at h1
      linarith
    · intro h
      by_contra hne
      obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have := X7M_mapsto lam ht
      rw [h] at this
      simp at this
  intro f
  induction f with
  | zero =>
    intro z e hz
    simp only [walkEval]
    by_cases h : successors (X7M_stair (corners lam).card) (X7M_pi lam z) = ∅
    · rw [if_pos ((hemp z hz).mpr h), if_pos h]; rfl
    · rw [if_neg (fun h' => h ((hemp z hz).mp h')), if_neg h]
  | succ f ih =>
    intro z e hz
    simp only [walkEval]
    by_cases h : successors (X7M_stair (corners lam).card) (X7M_pi lam z) = ∅
    · rw [if_pos ((hemp z hz).mpr h), if_pos h]; rfl
    rw [if_neg (fun h' => h ((hemp z hz).mp h')), if_neg h]
    have hIH : ∀ t ∈ modifiedSuccessors lam z,
        walkEval (modifiedSuccessors lam) x y f t (fun tail => e ((z :: tail).map (X7M_pi lam))) =
        walkEval (successors (X7M_stair (corners lam).card)) (X7M_X lam x) (X7M_Y lam y) f
          (X7M_pi lam t) (fun tail => e (X7M_pi lam z :: tail)) := by
      intro t ht
      have hfun : (fun tail => e ((z :: tail).map (X7M_pi lam))) =
          (fun p => (fun q => e (X7M_pi lam z :: q)) (p.map (X7M_pi lam))) := by
        funext tail; simp [List.map_cons]
      rw [hfun]
      exact ih t (fun q => e (X7M_pi lam z :: q)) ((X7M_msucc_iff lam z t).mp ht).1
    have hD : ∑ u ∈ modifiedSuccessors lam z, moveWeight x y z u =
        ∑ v ∈ successors (X7M_stair (corners lam).card) (X7M_pi lam z),
          moveWeight (X7M_X lam x) (X7M_Y lam y) (X7M_pi lam z) v := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := X7M_pi lam) (fun t ht => X7M_mapsto lam ht)]
      exact Finset.sum_congr rfl (fun v hv => X7M_fiber lam x y hz hv)
    rw [Finset.sum_congr rfl (fun t ht => by rw [hIH t ht]), hD,
      ← Finset.sum_fiberwise_of_maps_to (g := X7M_pi lam) (fun t ht => X7M_mapsto lam ht)]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have hc : ∀ t ∈ (modifiedSuccessors lam z).filter (fun t => X7M_pi lam t = v),
        moveWeight x y z t / (∑ v ∈ successors (X7M_stair (corners lam).card) (X7M_pi lam z),
          moveWeight (X7M_X lam x) (X7M_Y lam y) (X7M_pi lam z) v) *
        walkEval (successors (X7M_stair (corners lam).card)) (X7M_X lam x) (X7M_Y lam y) f
          (X7M_pi lam t) (fun tail => e (X7M_pi lam z :: tail)) =
        moveWeight x y z t / (∑ v ∈ successors (X7M_stair (corners lam).card) (X7M_pi lam z),
          moveWeight (X7M_X lam x) (X7M_Y lam y) (X7M_pi lam z) v) *
        walkEval (successors (X7M_stair (corners lam).card)) (X7M_X lam x) (X7M_Y lam y) f
          v (fun tail => e (X7M_pi lam z :: tail)) := by
      intro t ht
      rw [(Finset.mem_filter.mp ht).2]
    rw [Finset.sum_congr rfl hc, ← Finset.sum_mul, ← Finset.sum_div, X7M_fiber lam x y hz hv]

theorem X7M_find (S : Finset ℕ) (a t : ℕ) (ha : a ∈ S) :
    ((S.sort (· ≤ ·)).find? (fun r => decide (t ≤ r))).getD t = a ↔
      (t ≤ a ∧ ∀ b ∈ S, t ≤ b → a ≤ b) := by
  have hmem : ∀ b, b ∈ S.sort (· ≤ ·) ↔ b ∈ S := fun b => Finset.mem_sort _
  have hpw : (S.sort (· ≤ ·)).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  cases hf : (S.sort (· ≤ ·)).find? (fun r => decide (t ≤ r)) with
  | none =>
    simp only [Option.getD_none]
    rw [List.find?_eq_none] at hf
    constructor
    · rintro rfl
      have := hf t ((hmem t).mpr ha)
      simp at this
    · rintro ⟨h1, -⟩
      have := hf a ((hmem a).mpr ha)
      simp [h1] at this
  | some a' =>
    simp only [Option.getD_some]
    rw [List.find?_eq_some_iff_append] at hf
    obtain ⟨hpa, as, bs, hL, has⟩ := hf
    have ht' : t ≤ a' := by simpa using hpa
    have ha'S : a' ∈ S := (hmem a').mp (by rw [hL]; simp)
    have hleast : ∀ b ∈ S, t ≤ b → a' ≤ b := by
      intro b hb htb
      have hbL : b ∈ as ++ a' :: bs := by rw [← hL]; exact (hmem b).mpr hb
      rcases List.mem_append.mp hbL with h | h
      · have := has b h; simp [htb] at this
      · rcases List.mem_cons.mp h with rfl | h
        · exact le_rfl
        · rw [hL] at hpw
          have := List.pairwise_append.mp hpw
          exact (List.pairwise_cons.mp this.2.1).1 b h
    constructor
    · rintro rfl; exact ⟨ht', hleast⟩
    · rintro ⟨h1, h2⟩; exact le_antisymm (hleast a ha h1) (h2 a' ha'S ht')

theorem X7M_rowpart (lam : YoungDiagram) {zc : Cell} (hzc : zc ∈ corners lam) (t : ℕ) :
    ((rowEnds lam).find? (fun r => decide (t ≤ r))).getD t = zc.1 ↔
      X7M_rb lam t = X7M_rb lam zc.1 := by
  unfold rowEnds
  rw [X7M_find _ _ _ (Finset.mem_image.mpr ⟨zc, hzc, rfl⟩)]
  constructor
  · rintro ⟨h1, h2⟩
    have := X7M_rb_mono lam h1
    by_contra hne
    obtain ⟨c, hc, hc1, hc2⟩ := (X7M_rb_lt_iff lam t zc.1).mp (by omega)
    have := h2 c.1 (Finset.mem_image.mpr ⟨c, hc, rfl⟩) hc1
    omega
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hlt
      have := (X7M_rb_lt_iff lam zc.1 t).mpr ⟨zc, hzc, le_rfl, by omega⟩
      omega
    · intro b hb htb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
      by_contra hlt
      have := (X7M_rb_lt_iff lam t zc.1).mpr ⟨c, hc, htb, by omega⟩
      omega

theorem X7M_colpart (lam : YoungDiagram) {zc : Cell} (hzc : zc ∈ corners lam) (t : ℕ) :
    ((colEnds lam).find? (fun r => decide (t ≤ r))).getD t = zc.2 ↔
      X7M_cb lam t = X7M_cb lam zc.2 := by
  unfold colEnds
  rw [X7M_find _ _ _ (Finset.mem_image.mpr ⟨zc, hzc, rfl⟩)]
  constructor
  · rintro ⟨h1, h2⟩
    have := X7M_cb_mono lam h1
    by_contra hne
    obtain ⟨c, hc, hc1, hc2⟩ := (X7M_cb_lt_iff lam t zc.2).mp (by omega)
    have := h2 c.2 (Finset.mem_image.mpr ⟨c, hc, rfl⟩) hc1
    omega
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hlt
      have := (X7M_cb_lt_iff lam zc.2 t).mpr ⟨zc, hzc, le_rfl, by omega⟩
      omega
    · intro b hb htb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
      by_contra hlt
      have := (X7M_cb_lt_iff lam t zc.2).mpr ⟨c, hc, htb, by omega⟩
      omega

theorem X7M_bc (lam : YoungDiagram) {zc : Cell} (hzc : zc ∈ corners lam) (t : Cell) :
    blockCorner lam t = zc ↔ X7M_pi lam t = (X7M_rb lam zc.1, X7M_cb lam zc.2) := by
  unfold blockCorner X7M_pi
  rw [Prod.ext_iff, Prod.ext_iff]
  simp only
  rw [X7M_rowpart lam hzc, X7M_colpart lam hzc]

theorem X7M_event (lam : YoungDiagram) {zc : Cell} (hzc : zc ∈ corners lam) :
    (fun p : List Cell => if p.getLast?.map (blockCorner lam) = some zc then (1 : ℝ) else 0) =
    (fun p => (fun q : List Cell =>
      if q.getLast? = some (X7M_rb lam zc.1, X7M_cb lam zc.2) then (1 : ℝ) else 0)
        (p.map (X7M_pi lam))) := by
  funext p
  simp only [List.getLast?_map]
  cases p.getLast? with
  | none => simp
  | some t =>
    simp only [Option.map_some, Option.some.injEq]
    by_cases h : blockCorner lam t = zc
    · rw [if_pos h, if_pos ((X7M_bc lam hzc t).mp h)]
    · rw [if_neg h, if_neg (fun h' => h ((X7M_bc lam hzc t).mpr h'))]

theorem X7M_startsum (lam : YoungDiagram) (x y : ℕ → ℝ) (g : Cell → ℝ) :
    ∑ z ∈ lam.cells, x z.1 * y z.2 * g (X7M_pi lam z) =
      ∑ u ∈ (X7M_stair (corners lam).card).cells, X7M_X lam x u.1 * X7M_Y lam y u.2 * g u := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := X7M_pi lam)
    (t := (X7M_stair (corners lam).card).cells)
    (fun z hz => (YoungDiagram.mem_cells _).mpr (X7M_pi_mem lam ((YoungDiagram.mem_cells _).mp hz)))]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  rw [YoungDiagram.mem_cells, X7M_stair_mem] at hu
  have hset : lam.cells.filter (fun z => X7M_pi lam z = u) =
      ((Finset.range (lam.colLen 0)).filter (fun i => X7M_rb lam i = u.1)) ×ˢ
      ((Finset.range (lam.rowLen 0)).filter (fun j => X7M_cb lam j = u.2)) := by
    ext ⟨a, b⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_range, Finset.mem_range, YoungDiagram.mem_cells, X7M_mem_iff,
      X7M_row_iff, X7M_col_iff]
    simp only [X7M_pi, Prod.ext_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; refine ⟨⟨?_, h2⟩, ⟨?_, h3⟩⟩ <;> omega
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨by omega, h2, h4⟩
  rw [hset, Finset.sum_product]
  have hc : ∀ a ∈ (Finset.range (lam.colLen 0)).filter (fun i => X7M_rb lam i = u.1),
      ∑ b ∈ (Finset.range (lam.rowLen 0)).filter (fun j => X7M_cb lam j = u.2),
        x (a, b).1 * y (a, b).2 * g (X7M_pi lam (a, b)) =
      ∑ b ∈ (Finset.range (lam.rowLen 0)).filter (fun j => X7M_cb lam j = u.2),
        x a * y b * g u := by
    intro a ha
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have h1 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hb).2
    have : X7M_pi lam (a, b) = u := Prod.ext h1 h2
    rw [this]
  rw [Finset.sum_congr rfl hc, X7M_X, X7M_Y, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_mul]

theorem X7M_cb_succ (lam : YoungDiagram) (j : ℕ) : X7M_cb lam (j + 1) ≤ X7M_cb lam j + 1 := by
  unfold X7M_cb
  have hsub : (corners lam).filter (fun c => c.2 < j + 1) ⊆
      (corners lam).filter (fun c => c.2 < j) ∪ (corners lam).filter (fun c => c.2 = j) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc.2 with h | h
    · exact Or.inl ⟨hc.1, h⟩
    · exact Or.inr ⟨hc.1, h⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((corners lam).filter (fun c => c.2 < j))
    ((corners lam).filter (fun c => c.2 = j))
  have h3 : ((corners lam).filter (fun c => c.2 = j)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact X7M_inj2 ha.1 hb.1 (by rw [ha.2, hb.2])
  omega

theorem X7M_rb_succ (lam : YoungDiagram) (i : ℕ) : X7M_rb lam (i + 1) ≤ X7M_rb lam i + 1 := by
  unfold X7M_rb
  have hsub : (corners lam).filter (fun c => c.1 < i + 1) ⊆
      (corners lam).filter (fun c => c.1 < i) ∪ (corners lam).filter (fun c => c.1 = i) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc.2 with h | h
    · exact Or.inl ⟨hc.1, h⟩
    · exact Or.inr ⟨hc.1, h⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((corners lam).filter (fun c => c.1 < i))
    ((corners lam).filter (fun c => c.1 = i))
  have h3 : ((corners lam).filter (fun c => c.1 = i)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact X7M_inj1 ha.1 hb.1 (by rw [ha.2, hb.2])
  omega

theorem X7M_rowLen_iff (lam : YoungDiagram) {i i' : ℕ} (hi : i < lam.colLen 0)
    (hi' : i' < lam.colLen 0) : lam.rowLen i = lam.rowLen i' ↔ X7M_rb lam i = X7M_rb lam i' := by
  constructor
  · intro h
    have key : ∀ a, a < lam.colLen 0 → X7M_rb lam a + X7M_cb lam (lam.rowLen a - 1) + 1 =
        (corners lam).card := by
      intro a ha
      have h0 : 0 < lam.rowLen a := YoungDiagram.mem_iff_lt_rowLen.mp
        (YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_lt_of_le ha (lam.colLen_anti 0 0 le_rfl)))
      have h1 := (X7M_mem_iff lam (a, lam.rowLen a - 1)).mp
        (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      have h2 : ¬ (X7M_rb lam a + X7M_cb lam (lam.rowLen a) + 1 ≤ (corners lam).card) := by
        intro h'
        have := YoungDiagram.mem_iff_lt_rowLen.mp ((X7M_mem_iff lam (a, lam.rowLen a)).mpr h')
        omega
      have h3 := X7M_cb_succ lam (lam.rowLen a - 1)
      rw [Nat.sub_add_cancel h0] at h3
      simp only at h1
      omega
    have := key i hi; have := key i' hi'
    rw [h] at *
    omega
  · intro h
    apply X7M_eq_of_lt_iff
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, ← YoungDiagram.mem_iff_lt_rowLen, X7M_mem_iff,
      X7M_mem_iff]
    simp only
    rw [h]

theorem X7M_colLen_iff (lam : YoungDiagram) {j j' : ℕ} (hj : j < lam.rowLen 0)
    (hj' : j' < lam.rowLen 0) : lam.colLen j = lam.colLen j' ↔ X7M_cb lam j = X7M_cb lam j' := by
  constructor
  · intro h
    have key : ∀ a, a < lam.rowLen 0 → X7M_cb lam a + X7M_rb lam (lam.colLen a - 1) + 1 =
        (corners lam).card := by
      intro a ha
      have h0 : 0 < lam.colLen a := YoungDiagram.mem_iff_lt_colLen.mp
        (YoungDiagram.mem_iff_lt_rowLen.mpr (lt_of_lt_of_le ha (lam.rowLen_anti 0 0 le_rfl)))
      have h1 := (X7M_mem_iff lam (lam.colLen a - 1, a)).mp
        (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))
      have h2 : ¬ (X7M_rb lam (lam.colLen a) + X7M_cb lam a + 1 ≤ (corners lam).card) := by
        intro h'
        have := YoungDiagram.mem_iff_lt_colLen.mp ((X7M_mem_iff lam (lam.colLen a, a)).mpr h')
        omega
      have h3 := X7M_rb_succ lam (lam.colLen a - 1)
      rw [Nat.sub_add_cancel h0] at h3
      simp only at h1
      omega
    have := key j hj; have := key j' hj'
    rw [h] at *
    omega
  · intro h
    apply X7M_eq_of_lt_iff
    intro i
    rw [← YoungDiagram.mem_iff_lt_colLen, ← YoungDiagram.mem_iff_lt_colLen, X7M_mem_iff,
      X7M_mem_iff]
    simp only
    rw [h]

theorem X7M_count_lt (S : Finset ℕ) (m : ℕ) (hS : S.card = m) (k : ℕ) (hk : k < m) :
    (S.filter (fun b => b < S.orderEmbOfFin hS ⟨k, hk⟩)).card = k := by
  set f := S.orderEmbOfFin hS
  have hset : S.filter (fun b => b < f ⟨k, hk⟩) =
      (Finset.univ.filter (fun i : Fin m => i < ⟨k, hk⟩)).map f.toEmbedding := by
    ext b
    rw [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨hb, hlt⟩
      have : b ∈ Set.range f := by rw [Finset.range_orderEmbOfFin]; exact hb
      obtain ⟨i, rfl⟩ := this
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, f.lt_iff_lt.mp hlt⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem S hS i, f.lt_iff_lt.mpr (Finset.mem_filter.mp hi).2⟩
  rw [hset, Finset.card_map]
  have : Finset.univ.filter (fun i : Fin m => i < ⟨k, hk⟩) = Finset.Iio ⟨k, hk⟩ := by
    ext i; simp
  rw [this, Fin.card_Iio]

theorem X7M_rowEnds (lam : YoungDiagram) (k : ℕ) (hk : k < (corners lam).card) :
    X7M_rb lam ((rowEnds lam).getD k 0) = k ∧ (rowEnds lam).getD k 0 < lam.colLen 0 := by
  set S := (corners lam).image Prod.fst with hSdef
  have hS : S.card = (corners lam).card :=
    Finset.card_image_of_injOn (fun a ha b hb h => X7M_inj1 ha hb h)
  have hget : (rowEnds lam).getD k 0 = S.orderEmbOfFin hS ⟨k, hk⟩ := by
    rw [Finset.orderEmbOfFin_apply]
    unfold rowEnds
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
    rfl
  have hmem : (rowEnds lam).getD k 0 ∈ S := by rw [hget]; exact Finset.orderEmbOfFin_mem S hS _
  obtain ⟨c, hc, hc1⟩ := Finset.mem_image.mp hmem
  refine ⟨?_, ?_⟩
  · unfold X7M_rb
    have : ((corners lam).filter (fun c => c.1 < (rowEnds lam).getD k 0)).card =
        (S.filter (fun b => b < (rowEnds lam).getD k 0)).card := by
      rw [hSdef, Finset.filter_image]
      exact (Finset.card_image_of_injOn (fun a ha b hb h =>
        X7M_inj1 (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 h)).symm
    rw [this, hget]
    exact X7M_count_lt S _ hS k hk
  · rw [← hc1, X7M_row_iff]; exact X7M_rb_corner_lt lam hc

theorem X7M_colEnds (lam : YoungDiagram) (k : ℕ) (hk : k < (corners lam).card) :
    X7M_cb lam ((colEnds lam).getD k 0) = k ∧ (colEnds lam).getD k 0 < lam.rowLen 0 := by
  set S := (corners lam).image Prod.snd with hSdef
  have hS : S.card = (corners lam).card :=
    Finset.card_image_of_injOn (fun a ha b hb h => X7M_inj2 ha hb h)
  have hget : (colEnds lam).getD k 0 = S.orderEmbOfFin hS ⟨k, hk⟩ := by
    rw [Finset.orderEmbOfFin_apply]
    unfold colEnds
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
    rfl
  have hmem : (colEnds lam).getD k 0 ∈ S := by rw [hget]; exact Finset.orderEmbOfFin_mem S hS _
  obtain ⟨c, hc, hc1⟩ := Finset.mem_image.mp hmem
  refine ⟨?_, ?_⟩
  · unfold X7M_cb
    have : ((corners lam).filter (fun c => c.2 < (colEnds lam).getD k 0)).card =
        (S.filter (fun b => b < (colEnds lam).getD k 0)).card := by
      rw [hSdef, Finset.filter_image]
      exact (Finset.card_image_of_injOn (fun a ha b hb h =>
        X7M_inj2 (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 h)).symm
    rw [this, hget]
    exact X7M_count_lt S _ hS k hk
  · rw [← hc1, X7M_col_iff]; exact X7M_cb_corner_lt lam hc

theorem X7M_blockX (lam : YoungDiagram) (x : ℕ → ℝ) (k : ℕ) (hk : k < (corners lam).card) :
    blockX lam x k = X7M_X lam x k := by
  obtain ⟨h1, h2⟩ := X7M_rowEnds lam k hk
  unfold blockX X7M_X
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro i hi
  rw [X7M_rowLen_iff lam (Finset.mem_range.mp hi) h2, h1]

theorem X7M_blockY (lam : YoungDiagram) (y : ℕ → ℝ) (k : ℕ) (hk : k < (corners lam).card) :
    blockY lam y k = X7M_Y lam y k := by
  obtain ⟨h1, h2⟩ := X7M_colEnds lam k hk
  unfold blockY X7M_Y
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro j hj
  rw [X7M_colLen_iff lam (Finset.mem_range.mp hj) h2, h1]

theorem X7M_sw_congr (c r s : ℕ) (X X' Y Y' : ℕ → ℝ) (hX : ∀ k < c, X k = X' k)
    (hY : ∀ l < c, Y l = Y' l) (hr : r < c) (hs : s < c) :
    staircaseWeight c X Y r s = staircaseWeight c X' Y' r s := by
  unfold staircaseWeight
  have e1 : ∏ i ∈ Finset.range r, (1 + X i / ((∑ k ∈ Finset.Ico (i + 1) (r + 1), X k) +
        ∑ l ∈ Finset.Ico (s + 1) (c - i), Y l)) =
      ∏ i ∈ Finset.range r, (1 + X' i / ((∑ k ∈ Finset.Ico (i + 1) (r + 1), X' k) +
        ∑ l ∈ Finset.Ico (s + 1) (c - i), Y' l)) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [hX i (by omega), Finset.sum_congr rfl (fun k hk => hX k (by
      rw [Finset.mem_Ico] at hk; omega)), Finset.sum_congr rfl (fun l hl => hY l (by
      rw [Finset.mem_Ico] at hl; omega))]
  have e2 : ∏ j ∈ Finset.range s, (1 + Y j / ((∑ k ∈ Finset.Ico (r + 1) (c - j), X k) +
        ∑ l ∈ Finset.Ico (j + 1) (s + 1), Y l)) =
      ∏ j ∈ Finset.range s, (1 + Y' j / ((∑ k ∈ Finset.Ico (r + 1) (c - j), X' k) +
        ∑ l ∈ Finset.Ico (j + 1) (s + 1), Y' l)) := by
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    rw [hY j (by omega), Finset.sum_congr rfl (fun k hk => hX k (by
      rw [Finset.mem_Ico] at hk; omega)), Finset.sum_congr rfl (fun l hl => hY l (by
      rw [Finset.mem_Ico] at hl; omega))]
  rw [hX r hr, hY s hs, e1, e2]

end QAlgorithms.Papers.Independent.Next46.P26

end

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Next46.P26 in
theorem solution (lam : YoungDiagram) (hne : lam.cells.Nonempty)
    (x y : ℕ → ℝ) (hpos : PositiveWeights lam x y) (z : Cell) (hz : z ∈ corners lam) :
    modifiedTerminalProb lam x y z =
      staircaseWeight (corners lam).card (blockX lam x) (blockY lam y)
        (cornerRank lam z) ((corners lam).card - 1 - cornerRank lam z) /
      totalWeight lam x y := by
  obtain ⟨hx, hy⟩ := hpos
  have hrm : X7M_rb lam z.1 < (corners lam).card := X7M_rb_corner_lt lam hz
  have hcb : X7M_cb lam z.2 = (corners lam).card - 1 - X7M_rb lam z.1 := by
    have h1 := (X7M_mem_iff lam z).mp (X7M_cf hz).1
    have hz' : (z.1, z.2 + 1) ∉ lam := by
      have := hz; simp only [corners, Finset.mem_filter] at this; exact this.2.2
    have h2 : ¬ (X7M_rb lam z.1 + X7M_cb lam (z.2 + 1) + 1 ≤ (corners lam).card) :=
      fun h => hz' ((X7M_mem_iff lam (z.1, z.2 + 1)).mpr h)
    have h3 := X7M_cb_succ lam z.2
    omega
  have hW : totalWeight lam x y =
      totalWeight (X7M_stair (corners lam).card) (X7M_X lam x) (X7M_Y lam y) := by
    unfold totalWeight
    have := X7M_startsum lam x y (fun _ => 1)
    simpa using this
  have hposμ : PositiveWeights (X7M_stair (corners lam).card) (X7M_X lam x) (X7M_Y lam y) := by
    refine ⟨fun i hi => X7M_X_pos lam x hx i ?_, fun j hj => X7M_Y_pos lam y hy j ?_⟩
    · rw [X7M_stair_colLen] at hi; omega
    · rw [X7M_stair_rowLen] at hj; omega
  have hcard : (corners lam).card ≤ lam.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have htw := X7T_twalk (X7M_stair (corners lam).card) (X7M_X lam x) (X7M_Y lam y) hposμ
    (X7M_rb lam z.1) ((corners lam).card - 1 - X7M_rb lam z.1)
    (X7M_stair_corner _ _ hrm) lam.card (by omega)
  have key : ∀ z' ∈ lam.cells,
      walkEval (modifiedSuccessors lam) x y lam.card z'
        (fun p => if p.getLast?.map (blockCorner lam) = some z then 1 else 0) =
      walkEval (successors (X7M_stair (corners lam).card)) (X7M_X lam x) (X7M_Y lam y)
        lam.card (X7M_pi lam z')
        (fun q => if q.getLast? = some (X7M_rb lam z.1, X7M_cb lam z.2) then 1 else 0) := by
    intro z' hz'
    rw [X7M_event lam hz]
    exact X7M_transfer lam x y hx hy lam.card z'
      (fun q => if q.getLast? = some (X7M_rb lam z.1, X7M_cb lam z.2) then 1 else 0)
      ((YoungDiagram.mem_cells _).mp hz')
  have hsum : ∑ z' ∈ lam.cells, (x z'.1 * y z'.2 / totalWeight lam x y) *
      walkEval (modifiedSuccessors lam) x y lam.card z'
        (fun p => if p.getLast?.map (blockCorner lam) = some z then 1 else 0) =
      ∑ z' ∈ lam.cells, x z'.1 * y z'.2 *
        (walkEval (successors (X7M_stair (corners lam).card)) (X7M_X lam x) (X7M_Y lam y)
        lam.card (X7M_pi lam z')
        (fun q => if q.getLast? = some (X7M_rb lam z.1, X7M_cb lam z.2) then 1 else 0) /
          totalWeight lam x y) :=
    Finset.sum_congr rfl (fun z' hz' => by rw [key z' hz']; ring)
  unfold modifiedTerminalProb
  rw [hsum, X7M_startsum lam x y (fun u =>
    walkEval (successors (X7M_stair (corners lam).card)) (X7M_X lam x) (X7M_Y lam y)
        lam.card u
        (fun q => if q.getLast? = some (X7M_rb lam z.1, X7M_cb lam z.2) then 1 else 0) /
          totalWeight lam x y), hW, hcb]
  have hcw : cornerWeight (X7M_stair (corners lam).card) (X7M_X lam x) (X7M_Y lam y)
      (X7M_rb lam z.1) ((corners lam).card - 1 - X7M_rb lam z.1) =
      staircaseWeight (corners lam).card (X7M_X lam x) (X7M_Y lam y)
      (X7M_rb lam z.1) ((corners lam).card - 1 - X7M_rb lam z.1) := by
    unfold cornerWeight staircaseWeight rowGap colGap
    simp only [X7M_stair_rowLen, X7M_stair_colLen]
  have hsw := X7M_sw_congr (corners lam).card (X7M_rb lam z.1)
    ((corners lam).card - 1 - X7M_rb lam z.1) (X7M_X lam x) (blockX lam x) (X7M_Y lam y)
    (blockY lam y) (fun k hk => (X7M_blockX lam x k hk).symm)
    (fun l hl => (X7M_blockY lam y l hl).symm) hrm (by omega)
  show _ = staircaseWeight (corners lam).card (blockX lam x) (blockY lam y)
    (X7M_rb lam z.1) ((corners lam).card - 1 - X7M_rb lam z.1) / _
  rw [← hsw, ← hcw, ← htw]
  exact Finset.sum_congr rfl (fun u _ => by ring)

end
