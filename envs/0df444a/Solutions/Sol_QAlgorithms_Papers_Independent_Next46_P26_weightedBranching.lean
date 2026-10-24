-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P26.weightedBranching
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:24:38.792814+00:00
-- url     : https://prove2.me/submissions/19e49975-907a-4dd3-b81a-d65bbc579ee8

import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P26_weightedHookWalk

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem X7hk_walk_sum (next : Cell → Finset Cell) (x y : ℕ → ℝ) {ι : Type*} (S : Finset ι) :
    ∀ (fuel : ℕ) (z : Cell) (f : ι → List Cell → ℝ),
      walkEval next x y fuel z (fun p => ∑ c ∈ S, f c p) =
        ∑ c ∈ S, walkEval next x y fuel z (f c) := by
  intro fuel
  induction fuel with
  | zero =>
    intro z f
    simp only [walkEval]
    split_ifs <;> simp
  | succ n ih =>
    intro z f
    simp only [walkEval]
    split_ifs with h
    · rfl
    · have := fun t => ih t (fun c tail => f c (z :: tail))
      simp only [this, Finset.mul_sum]
      exact Finset.sum_comm

theorem X7hk_mem_lam {lam : YoungDiagram} {t : Cell} (ht : t ∈ lam) :
    t.1 < lam.colLen 0 ∧ t.2 < lam.rowLen 0 := by
  have h1 : t.1 < lam.colLen t.2 := YoungDiagram.mem_iff_lt_colLen.mp (by simpa using ht)
  have h2 : t.2 < lam.rowLen t.1 := YoungDiagram.mem_iff_lt_rowLen.mp (by simpa using ht)
  exact ⟨lt_of_lt_of_le h1 (lam.colLen_anti 0 t.2 (Nat.zero_le _)),
    lt_of_lt_of_le h2 (lam.rowLen_anti 0 t.1 (Nat.zero_le _))⟩

theorem X7hk_succ_empty {lam : YoungDiagram} {z : Cell} (hz : z ∈ lam.cells)
    (h : successors lam z = ∅) : z ∈ corners lam := by
  simp only [corners, Finset.mem_filter]
  refine ⟨hz, ?_, ?_⟩
  · intro hm
    have : (z.1 + 1, z.2) ∈ successors lam z := by
      simp [successors, hm]
    simp [h] at this
  · intro hm
    have : (z.1, z.2 + 1) ∈ successors lam z := by
      simp [successors, hm]
    simp [h] at this

theorem X7hk_walk_one (lam : YoungDiagram) :
    ∀ (fuel : ℕ) (z : Cell), z ∈ lam.cells →
      lam.colLen 0 + lam.rowLen 0 ≤ fuel + z.1 + z.2 + 2 →
      ∀ E : List Cell → ℝ, (∀ l c, c ∈ corners lam → E (l ++ [c]) = 1) →
        walkEval (successors lam) (fun _ => 1) (fun _ => 1) fuel z E = 1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro z hz hf E hE
    have hs : successors lam z = ∅ := by
      ext t
      simp only [successors, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro ht h
      have := X7hk_mem_lam (lam := lam) ht
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    simp only [walkEval, hs, if_true]
    simpa using hE [] z (X7hk_succ_empty hz hs)
  | succ n ih =>
    intro z hz hf E hE
    simp only [walkEval]
    split_ifs with h
    · simpa using hE [] z (X7hk_succ_empty hz h)
    · have hne : (successors lam z).Nonempty := Finset.nonempty_iff_ne_empty.mpr h
      have hw : ∀ t u : Cell, moveWeight (fun _ => (1:ℝ)) (fun _ => 1) t u = 1 := by
        intro t u; simp [moveWeight]
      have hcard : ((successors lam z).card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_pos.mpr hne).ne'
      have key : ∀ t ∈ successors lam z,
          walkEval (successors lam) (fun _ => 1) (fun _ => 1) n t (fun tail => E (z :: tail)) = 1 := by
        intro t ht
        simp only [successors, Finset.mem_filter] at ht
        apply ih t ht.1
        · rcases ht.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        · intro l c hc
          simpa using hE (z :: l) c hc
      rw [Finset.sum_congr rfl (fun t ht => by rw [key t ht])]
      simp only [hw, Finset.sum_const, nsmul_eq_mul, mul_one]
      field_simp

theorem X7hk_card_bound (lam : YoungDiagram) : lam.colLen 0 + lam.rowLen 0 ≤ lam.card + 1 := by
  let A := (Finset.range (lam.rowLen 0)).image fun j => ((0 : ℕ), j)
  let B := (Finset.Ico 1 (lam.colLen 0)).image fun i => (i, (0 : ℕ))
  have hA : A.card = lam.rowLen 0 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]; simp
  have hB : B.card = lam.colLen 0 - 1 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]; simp
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [A, B, Finset.mem_image, Finset.mem_range, Finset.mem_Ico] at ha hb
    obtain ⟨j, -, rfl⟩ := ha
    obtain ⟨i, hi, he⟩ := hb
    simp only [Prod.mk.injEq] at he
    omega
  have hsub : A ∪ B ⊆ lam.cells := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · simp only [A, Finset.mem_image, Finset.mem_range] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      exact YoungDiagram.mem_iff_lt_rowLen.mpr hj
    · simp only [B, Finset.mem_image, Finset.mem_Ico] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact YoungDiagram.mem_iff_lt_colLen.mpr hi.2
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hA, hB] at this
  unfold YoungDiagram.card
  omega

/-- Total terminal mass of the unit-weight walk is one. -/
theorem X7hk_total (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    ∑ c ∈ corners lam, terminalProb lam (successors lam) (fun _ => 1) (fun _ => 1) c = 1 := by
  unfold terminalProb
  rw [Finset.sum_comm]
  have hW : totalWeight lam (fun _ => (1:ℝ)) (fun _ => 1) = lam.card := by
    simp [totalWeight, YoungDiagram.card]
  have hn : (lam.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hne).ne'
  have : ∀ z ∈ lam.cells,
      ∑ c ∈ corners lam, (1 * 1 / totalWeight lam (fun _ => (1:ℝ)) (fun _ => 1)) *
        walkEval (successors lam) (fun _ => 1) (fun _ => 1) lam.card z
          (fun p => if p.getLast? = some c then 1 else 0) = 1 / lam.card := by
    intro z hz
    rw [← Finset.mul_sum, ← X7hk_walk_sum, X7hk_walk_one lam lam.card z hz, hW]
    · simp
    · have := X7hk_card_bound lam; omega
    · intro l c hc
      simp [Finset.sum_ite_eq', hc]
  rw [Finset.sum_congr rfl this]
  simp only [Finset.sum_const, nsmul_eq_mul]
  unfold YoungDiagram.card at hn ⊢
  field_simp

end QAlgorithms.Papers.Independent.Next46.P26

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem X7hk_arm (lam : YoungDiagram) (i j : ℕ) :
    (lam.cells.filter fun a => a.1 = i ∧ j < a.2).card = lam.rowLen i - (j + 1) := by
  have : (lam.cells.filter fun a => a.1 = i ∧ j < a.2) =
      (Finset.Ico (j + 1) (lam.rowLen i)).image fun l => (i, l) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
    constructor
    · rintro ⟨h, rfl, hb⟩
      exact ⟨b, ⟨hb, YoungDiagram.mem_iff_lt_rowLen.mp h⟩, rfl, rfl⟩
    · rintro ⟨l, ⟨h1, h2⟩, rfl, rfl⟩
      exact ⟨YoungDiagram.mem_iff_lt_rowLen.mpr h2, rfl, h1⟩
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp

theorem X7hk_leg (lam : YoungDiagram) (i j : ℕ) :
    (lam.cells.filter fun a => a.2 = j ∧ i < a.1).card = lam.colLen j - (i + 1) := by
  have : (lam.cells.filter fun a => a.2 = j ∧ i < a.1) =
      (Finset.Ico (i + 1) (lam.colLen j)).image fun k => (k, j) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
    constructor
    · rintro ⟨h, rfl, hb⟩
      exact ⟨a, ⟨hb, YoungDiagram.mem_iff_lt_colLen.mp h⟩, rfl, rfl⟩
    · rintro ⟨l, ⟨h1, h2⟩, rfl, rfl⟩
      exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr h2, rfl, h1⟩
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp

theorem X7hk_hook (lam : YoungDiagram) (i j : ℕ) :
    hook lam (i, j) = 1 + (lam.rowLen i - (j + 1)) + (lam.colLen j - (i + 1)) := by
  simp only [hook, QAlgorithms.Papers.Independent.Dependency50.P31.cellHook]
  rw [X7hk_arm, X7hk_leg]

theorem X7hk_corner {lam : YoungDiagram} {r s : ℕ} (hc : (r, s) ∈ corners lam) :
    (r, s) ∈ lam ∧ lam.colLen s = r + 1 ∧ lam.rowLen r = s + 1 := by
  simp only [corners, Finset.mem_filter] at hc
  obtain ⟨h0, h1, h2⟩ := hc
  have hm : (r, s) ∈ lam := by simpa using h0
  refine ⟨hm, ?_, ?_⟩
  · have a := YoungDiagram.mem_iff_lt_colLen.mp hm
    have b : ¬ r + 1 < lam.colLen s := fun h => h1 (by simpa using YoungDiagram.mem_iff_lt_colLen.mpr h)
    omega
  · have a := YoungDiagram.mem_iff_lt_rowLen.mp hm
    have b : ¬ s + 1 < lam.rowLen r := fun h => h2 (by simpa using YoungDiagram.mem_iff_lt_rowLen.mpr h)
    omega

/-- Column cells above a corner have hook ≥ 2 and rowGap = hook - 1. -/
theorem X7hk_col {lam : YoungDiagram} {r s i : ℕ} (hc : (r, s) ∈ corners lam) (hi : i < r) :
    2 ≤ hook lam (i, s) ∧
      rowGap lam (fun _ => (1:ℝ)) (fun _ => 1) i r s = (hook lam (i, s) : ℝ) - 1 := by
  obtain ⟨hm, hcol, hrow⟩ := X7hk_corner hc
  have hin : (i, s) ∈ lam := lam.isLowerSet (show (i, s) ≤ (r, s) from ⟨hi.le, le_rfl⟩) hm
  have hl := YoungDiagram.mem_iff_lt_rowLen.mp hin
  rw [X7hk_hook, hcol]
  refine ⟨by omega, ?_⟩
  simp only [rowGap, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  have e1 : r + 1 - (i + 1) = r - i := by omega
  rw [e1]
  push_cast
  ring

theorem X7hk_row {lam : YoungDiagram} {r s j : ℕ} (hc : (r, s) ∈ corners lam) (hj : j < s) :
    2 ≤ hook lam (r, j) ∧
      colGap lam (fun _ => (1:ℝ)) (fun _ => 1) j r s = (hook lam (r, j) : ℝ) - 1 := by
  obtain ⟨hm, hcol, hrow⟩ := X7hk_corner hc
  have hin : (r, j) ∈ lam := lam.isLowerSet (show (r, j) ≤ (r, s) from ⟨le_rfl, hj.le⟩) hm
  have hl := YoungDiagram.mem_iff_lt_colLen.mp hin
  rw [X7hk_hook, hrow]
  refine ⟨by omega, ?_⟩
  simp only [colGap, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  have e1 : s + 1 - (j + 1) = s - j := by omega
  rw [e1]
  push_cast
  ring

/-- Clause (3) over ℝ. -/
theorem X7hk_clause3R (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    ∑ z ∈ corners lam, (1 / (lam.card : ℝ)) *
      (∏ i ∈ Finset.range z.1,
        (hook lam (i, z.2) : ℝ) / ((hook lam (i, z.2) : ℝ) - 1)) *
      ∏ j ∈ Finset.range z.2,
        (hook lam (z.1, j) : ℝ) / ((hook lam (z.1, j) : ℝ) - 1) = 1 := by
  refine Eq.trans (Finset.sum_congr rfl ?_) (X7hk_total lam hne)
  rintro ⟨r, s⟩ hc
  have hpos : PositiveWeights lam (fun _ => (1:ℝ)) (fun _ => 1) := ⟨fun _ _ => one_pos, fun _ _ => one_pos⟩
  rw [weightedHookWalk lam hne _ _ hpos (r, s) hc]
  have hW : totalWeight lam (fun _ => (1:ℝ)) (fun _ => 1) = lam.card := by
    simp [totalWeight, YoungDiagram.card]
  rw [hW]
  simp only [cornerWeight, one_mul]
  have hP : (∏ i ∈ Finset.range r, (hook lam (i, s) : ℝ) / ((hook lam (i, s) : ℝ) - 1)) =
      ∏ i ∈ Finset.range r, (1 + 1 / rowGap lam (fun _ => (1:ℝ)) (fun _ => 1) i r s) := by
    apply Finset.prod_congr rfl
    intro i hi
    obtain ⟨h2, hg⟩ := X7hk_col hc (Finset.mem_range.mp hi)
    rw [hg]
    have : (hook lam (i, s) : ℝ) - 1 ≠ 0 := by
      have : (2:ℝ) ≤ hook lam (i, s) := by exact_mod_cast h2
      linarith
    field_simp
    ring
  have hQ : (∏ j ∈ Finset.range s, (hook lam (r, j) : ℝ) / ((hook lam (r, j) : ℝ) - 1)) =
      ∏ j ∈ Finset.range s, (1 + 1 / colGap lam (fun _ => (1:ℝ)) (fun _ => 1) j r s) := by
    apply Finset.prod_congr rfl
    intro j hj
    obtain ⟨h2, hg⟩ := X7hk_row hc (Finset.mem_range.mp hj)
    rw [hg]
    have : (hook lam (r, j) : ℝ) - 1 ≠ 0 := by
      have : (2:ℝ) ≤ hook lam (r, j) := by exact_mod_cast h2
      linarith
    field_simp
    ring
  simp only at hP hQ ⊢
  rw [hP, hQ]
  ring

/-- Clause (3) over ℚ. -/
theorem X7hk_clause3 (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    ∑ z ∈ corners lam, (1 / (lam.card : ℚ)) *
      (∏ i ∈ Finset.range z.1,
        (hook lam (i, z.2) : ℚ) / ((hook lam (i, z.2) : ℚ) - 1)) *
      ∏ j ∈ Finset.range z.2,
        (hook lam (z.1, j) : ℚ) / ((hook lam (z.1, j) : ℚ) - 1) = 1 := by
  have := X7hk_clause3R lam hne
  apply (Rat.cast_injective (α := ℝ))
  push_cast
  exact this

end QAlgorithms.Papers.Independent.Next46.P26

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem X7hk_prod_cross {M : Type*} [CommMonoid M] (T : Finset Cell) (r s : ℕ) (g : Cell → M)
    (hA : ∀ i < r, (i, s) ∈ T) (hB : ∀ j < s, (r, j) ∈ T)
    (hT : ∀ z ∈ T, ¬(z.1 ≠ r ∧ z.2 ≠ s) → (z.1 < r ∧ z.2 = s) ∨ (z.1 = r ∧ z.2 < s)) :
    ∏ z ∈ T, g z = (∏ i ∈ Finset.range r, g (i, s)) * (∏ j ∈ Finset.range s, g (r, j)) *
      ∏ z ∈ T.filter (fun z => z.1 ≠ r ∧ z.2 ≠ s), g z := by
  rw [← Finset.prod_filter_mul_prod_filter_not T (fun z => z.1 ≠ r ∧ z.2 ≠ s), mul_comm]
  congr 1
  have hE : T.filter (fun z => ¬(z.1 ≠ r ∧ z.2 ≠ s)) =
      (Finset.range r).image (fun i => (i, s)) ∪ (Finset.range s).image (fun j => (r, j)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_range,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hz, hn⟩
      rcases hT _ hz hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨a, h1, rfl, h2.symm⟩
      · exact Or.inr ⟨b, h2, h1.symm, rfl⟩
    · rintro (⟨i, hi, rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩)
      · exact ⟨hA i hi, by simp⟩
      · exact ⟨hB j hj, by simp⟩
  rw [hE, Finset.prod_union, Finset.prod_image (fun a _ b _ h => by simpa using h),
    Finset.prod_image (fun a _ b _ h => by simpa using h)]
  rw [Finset.disjoint_left]
  rintro ⟨a, b⟩ h1 h2
  simp only [Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at h1 h2
  obtain ⟨i, hi, rfl, rfl⟩ := h1
  obtain ⟨j, hj, h3, rfl⟩ := h2
  omega

theorem X7hk_hook_ge (lam : YoungDiagram) (z : Cell) : 1 ≤ hook lam z := by
  simp only [hook, QAlgorithms.Papers.Independent.Dependency50.P31.cellHook]; omega

/-- Cross structure of the noncorners around a corner. -/
theorem X7hk_noncorner_cross {lam : YoungDiagram} {r s : ℕ} (hc : (r, s) ∈ corners lam) :
    (∀ i < r, (i, s) ∈ noncorners lam) ∧ (∀ j < s, (r, j) ∈ noncorners lam) ∧
    (∀ z ∈ noncorners lam, ¬(z.1 ≠ r ∧ z.2 ≠ s) → (z.1 < r ∧ z.2 = s) ∨ (z.1 = r ∧ z.2 < s)) := by
  obtain ⟨hm, hcol, hrow⟩ := X7hk_corner hc
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have h1 : (i + 1, s) ∈ lam := lam.isLowerSet (show (i + 1, s) ≤ (r, s) from ⟨hi, le_rfl⟩) hm
    have h0 : (i, s) ∈ lam := lam.isLowerSet (show (i, s) ≤ (r, s) from ⟨hi.le, le_rfl⟩) hm
    simp only [noncorners, corners, Finset.mem_sdiff, Finset.mem_filter]
    exact ⟨by simpa using h0, fun h => h.2.1 (by simpa using h1)⟩
  · intro j hj
    have h1 : (r, j + 1) ∈ lam := lam.isLowerSet (show (r, j + 1) ≤ (r, s) from ⟨le_rfl, hj⟩) hm
    have h0 : (r, j) ∈ lam := lam.isLowerSet (show (r, j) ≤ (r, s) from ⟨le_rfl, hj.le⟩) hm
    simp only [noncorners, corners, Finset.mem_sdiff, Finset.mem_filter]
    exact ⟨by simpa using h0, fun h => h.2.2 (by simpa using h1)⟩
  · rintro ⟨a, b⟩ hz hn
    simp only [noncorners, Finset.mem_sdiff] at hz
    have hz1 : (a, b) ∈ lam := by simpa using hz.1
    have hne : (a, b) ≠ (r, s) := fun h => hz.2 (h ▸ hc)
    simp only [ne_eq, not_and, not_not] at hn
    by_cases ha : a = r
    · subst ha
      have := YoungDiagram.mem_iff_lt_rowLen.mp hz1
      have : b ≠ s := fun h => hne (by rw [h])
      right; constructor <;> omega
    · have hb := hn ha
      subst hb
      have := YoungDiagram.mem_iff_lt_colLen.mp hz1
      left; constructor <;> omega

/-- Clause (4). -/
theorem X7hk_clause4 (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    (lam.card : ℚ) * (∏ z ∈ noncorners lam, ((hook lam z : ℚ) - 1)) =
      ∑ z ∈ corners lam,
        (∏ i ∈ Finset.range z.1, (hook lam (i, z.2) : ℚ)) *
        (∏ j ∈ Finset.range z.2, (hook lam (z.1, j) : ℚ)) *
        ∏ u ∈ offCross lam z.1 z.2, ((hook lam u : ℚ) - 1) := by
  have h3 := X7hk_clause3 lam hne
  have hn : (lam.card : ℚ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hne).ne'
  have e : (lam.card : ℚ) * (∏ z ∈ noncorners lam, ((hook lam z : ℚ) - 1)) =
      (lam.card : ℚ) * (∏ z ∈ noncorners lam, ((hook lam z : ℚ) - 1)) *
        ∑ z ∈ corners lam, (1 / (lam.card : ℚ)) *
          (∏ i ∈ Finset.range z.1,
            (hook lam (i, z.2) : ℚ) / ((hook lam (i, z.2) : ℚ) - 1)) *
          ∏ j ∈ Finset.range z.2,
            (hook lam (z.1, j) : ℚ) / ((hook lam (z.1, j) : ℚ) - 1) := by
    rw [h3, mul_one]
  rw [e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨r, s⟩ hc
  dsimp only
  obtain ⟨hA, hB, hT⟩ := X7hk_noncorner_cross hc
  rw [X7hk_prod_cross _ r s (fun z => (hook lam z : ℚ) - 1) hA hB hT]
  simp only [offCross]
  have hP : (∏ i ∈ Finset.range r, ((hook lam (i, s) : ℚ) - 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    have := (X7hk_col hc (Finset.mem_range.mp hi)).1
    have : (2:ℚ) ≤ hook lam (i, s) := by exact_mod_cast this
    linarith
  have hQ : (∏ j ∈ Finset.range s, ((hook lam (r, j) : ℚ) - 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    have := (X7hk_row hc (Finset.mem_range.mp hj)).1
    have : (2:ℚ) ≤ hook lam (r, j) := by exact_mod_cast this
    linarith
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
  field_simp

theorem X7hk_mem_preds (lam mu : YoungDiagram) :
    mu ∈ oneBoxPredecessors lam ↔ mu.cells ⊆ lam.cells ∧ mu.cells.card + 1 = lam.card := by
  simp only [oneBoxPredecessors, Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨⟨a, ha⟩, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_powerset] at ha
    exact ⟨ha.1, ha.2.1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨mu.cells, ?_⟩, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h1, h2, mu.isLowerSet⟩

/-- The diagram obtained by removing a corner. -/
def X7hk_rem (lam : YoungDiagram) (c : Cell) (hc : c ∈ corners lam) : YoungDiagram :=
  ⟨lam.cells.erase c, by
    intro a b hba ha
    have ha' : a ∈ lam.cells.erase c := ha
    rw [Finset.mem_erase] at ha'
    show b ∈ lam.cells.erase c
    rw [Finset.mem_erase]
    have hb : b ∈ lam.cells := lam.isLowerSet hba ha'.2
    refine ⟨?_, hb⟩
    rintro rfl
    apply ha'.1
    simp only [corners, Finset.mem_filter] at hc
    obtain ⟨-, h1, h2⟩ := hc
    obtain ⟨hb1, hb2⟩ := hba
    rcases Nat.lt_or_ge b.1 a.1 with h | h
    · exact absurd (lam.isLowerSet (show (b.1 + 1, b.2) ≤ a from ⟨h, hb2⟩) ha'.2) (by simpa using h1)
    rcases Nat.lt_or_ge b.2 a.2 with h' | h'
    · exact absurd (lam.isLowerSet (show (b.1, b.2 + 1) ≤ a from ⟨hb1, h'⟩) ha'.2) (by simpa using h2)
    exact Prod.ext (le_antisymm h hb1) (le_antisymm h' hb2)⟩

theorem X7hk_sum_preds (lam : YoungDiagram) (F : YoungDiagram → ℚ) :
    ∑ mu ∈ oneBoxPredecessors lam, F mu =
      ∑ c ∈ (corners lam).attach, F (X7hk_rem lam c.1 c.2) := by
  symm
  apply Finset.sum_bij (fun c _ => X7hk_rem lam c.1 c.2)
  · rintro ⟨c, hc⟩ -
    rw [X7hk_mem_preds]
    have hcl : c ∈ lam.cells := (Finset.mem_filter.mp hc).1
    refine ⟨Finset.erase_subset _ _, ?_⟩
    show (lam.cells.erase c).card + 1 = lam.cells.card
    rw [Finset.card_erase_of_mem hcl]
    have := Finset.card_pos.mpr ⟨c, hcl⟩
    omega
  · rintro ⟨c, hc⟩ - ⟨d, hd⟩ - h
    have h' : lam.cells.erase c = lam.cells.erase d := congrArg YoungDiagram.cells h
    have hcl : c ∈ lam.cells := (Finset.mem_filter.mp hc).1
    by_contra hne
    have hcd : c ≠ d := fun e => hne (Subtype.ext e)
    have : c ∈ lam.cells.erase d := Finset.mem_erase.mpr ⟨hcd, hcl⟩
    rw [← h'] at this
    simp at this
  · intro mu hmu
    rw [X7hk_mem_preds] at hmu
    obtain ⟨hsub, hcard⟩ := hmu
    have : (lam.cells \ mu.cells).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub]
      unfold YoungDiagram.card at hcard
      omega
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp this
    have hcl : c ∈ lam.cells := (Finset.mem_sdiff.mp (hc ▸ Finset.mem_singleton_self c)).1
    have hcm : c ∉ mu.cells := (Finset.mem_sdiff.mp (hc ▸ Finset.mem_singleton_self c)).2
    have hmu_eq : mu.cells = lam.cells.erase c := by
      ext z
      rw [Finset.mem_erase]
      constructor
      · intro hz
        exact ⟨fun e => hcm (e ▸ hz), hsub hz⟩
      · rintro ⟨hzc, hz⟩
        by_contra hzm
        have : z ∈ lam.cells \ mu.cells := Finset.mem_sdiff.mpr ⟨hz, hzm⟩
        rw [hc] at this
        exact hzc (Finset.mem_singleton.mp this)
    have hcor : c ∈ corners lam := by
      simp only [corners, Finset.mem_filter]
      refine ⟨hcl, ?_, ?_⟩
      · intro h
        have h1 : (c.1 + 1, c.2) ∈ mu.cells := by
          rw [hmu_eq, Finset.mem_erase]
          refine ⟨?_, by simpa using h⟩
          intro e; have := congrArg Prod.fst e; simp at this
        exact hcm (mu.isLowerSet (show c ≤ (c.1 + 1, c.2) from ⟨Nat.le_succ _, le_rfl⟩) h1)
      · intro h
        have h1 : (c.1, c.2 + 1) ∈ mu.cells := by
          rw [hmu_eq, Finset.mem_erase]
          refine ⟨?_, by simpa using h⟩
          intro e; have := congrArg Prod.snd e; simp at this
        exact hcm (mu.isLowerSet (show c ≤ (c.1, c.2 + 1) from ⟨le_rfl, Nat.le_succ _⟩) h1)
    refine ⟨⟨c, hcor⟩, Finset.mem_attach _ _, ?_⟩
    cases mu
    simp only [X7hk_rem] at hmu_eq ⊢
    subst hmu_eq
    rfl
  · intro _ _; rfl

/-- Hooks after removing a corner. -/
theorem X7hk_hook_rem (lam : YoungDiagram) {r s : ℕ} (hc : (r, s) ∈ corners lam) (z : Cell) :
    hook (X7hk_rem lam (r, s) hc) z + (if z.1 < r ∧ z.2 = s then 1 else 0) +
      (if z.1 = r ∧ z.2 < s then 1 else 0) = hook lam z := by
  have hcl : (r, s) ∈ lam.cells := (Finset.mem_filter.mp hc).1
  simp only [hook, QAlgorithms.Papers.Independent.Dependency50.P31.cellHook, X7hk_rem,
    Finset.filter_erase]
  have e1 : ((lam.cells.filter fun a => a.1 = z.1 ∧ z.2 < a.2).erase (r, s)).card +
      (if z.1 = r ∧ z.2 < s then 1 else 0) =
      (lam.cells.filter fun a => a.1 = z.1 ∧ z.2 < a.2).card := by
    split_ifs with h
    · exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hcl, h.1.symm, h.2⟩)
    · rw [Finset.erase_eq_of_notMem]
      · rfl
      · intro hm
        exact h ⟨(Finset.mem_filter.mp hm).2.1.symm, (Finset.mem_filter.mp hm).2.2⟩
  have e2 : ((lam.cells.filter fun a => a.2 = z.2 ∧ z.1 < a.1).erase (r, s)).card +
      (if z.1 < r ∧ z.2 = s then 1 else 0) =
      (lam.cells.filter fun a => a.2 = z.2 ∧ z.1 < a.1).card := by
    split_ifs with h
    · exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hcl, h.2.symm, h.1⟩)
    · rw [Finset.erase_eq_of_notMem]
      · rfl
      · intro hm
        exact h ⟨(Finset.mem_filter.mp hm).2.2, (Finset.mem_filter.mp hm).2.1.symm⟩
  omega

/-- Hook products of λ and of λ minus a corner, as cross products. -/
theorem X7hk_hookProducts (lam : YoungDiagram) {r s : ℕ} (hc : (r, s) ∈ corners lam) :
    let R := ∏ z ∈ (lam.cells.erase (r, s)).filter (fun z => z.1 ≠ r ∧ z.2 ≠ s), (hook lam z : ℚ)
    hookProduct lam = (∏ i ∈ Finset.range r, (hook lam (i, s) : ℚ)) *
        (∏ j ∈ Finset.range s, (hook lam (r, j) : ℚ)) * R ∧
    hookProduct (X7hk_rem lam (r, s) hc) = (∏ i ∈ Finset.range r, ((hook lam (i, s) : ℚ) - 1)) *
        (∏ j ∈ Finset.range s, ((hook lam (r, j) : ℚ) - 1)) * R := by
  intro R
  have hcl : (r, s) ∈ lam.cells := (Finset.mem_filter.mp hc).1
  obtain ⟨hm, hcol, hrow⟩ := X7hk_corner hc
  have hA : ∀ i < r, (i, s) ∈ lam.cells.erase (r, s) := by
    intro i hi
    rw [Finset.mem_erase]
    refine ⟨fun e => by simp at e; omega, ?_⟩
    simpa using lam.isLowerSet (show (i, s) ≤ (r, s) from ⟨hi.le, le_rfl⟩) hm
  have hB : ∀ j < s, (r, j) ∈ lam.cells.erase (r, s) := by
    intro j hj
    rw [Finset.mem_erase]
    refine ⟨fun e => by simp at e; omega, ?_⟩
    simpa using lam.isLowerSet (show (r, j) ≤ (r, s) from ⟨le_rfl, hj.le⟩) hm
  have hT : ∀ z ∈ lam.cells.erase (r, s), ¬(z.1 ≠ r ∧ z.2 ≠ s) →
      (z.1 < r ∧ z.2 = s) ∨ (z.1 = r ∧ z.2 < s) := by
    rintro ⟨a, b⟩ hz hn
    rw [Finset.mem_erase] at hz
    have hz1 : (a, b) ∈ lam := by simpa using hz.2
    simp only [ne_eq, not_and, not_not] at hn
    by_cases ha : a = r
    · subst ha
      have := YoungDiagram.mem_iff_lt_rowLen.mp hz1
      have : b ≠ s := fun h => hz.1 (by rw [h])
      right; constructor <;> omega
    · have hb := hn ha
      subst hb
      have := YoungDiagram.mem_iff_lt_colLen.mp hz1
      left; constructor <;> omega
  have hcs : hook lam (r, s) = 1 := by
    rw [X7hk_hook, hcol, hrow]; omega
  constructor
  · unfold hookProduct
    rw [← Finset.mul_prod_erase _ _ hcl, hcs, Nat.cast_one, one_mul]
    exact X7hk_prod_cross _ r s _ hA hB hT
  · unfold hookProduct
    show ∏ z ∈ lam.cells.erase (r, s), (hook (X7hk_rem lam (r, s) hc) z : ℚ) = _
    rw [X7hk_prod_cross _ r s _ hA hB hT]
    congr 1
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      have := X7hk_hook_rem lam hc (i, s)
      have hi' := Finset.mem_range.mp hi
      simp only [hi', and_self, if_true, lt_irrefl, false_and, and_false, if_false, add_zero] at this
      have : (hook lam (i, s) : ℚ) = hook (X7hk_rem lam (r, s) hc) (i, s) + 1 := by
        exact_mod_cast (by omega : hook lam (i, s) = hook (X7hk_rem lam (r, s) hc) (i, s) + 1)
      rw [this]; ring
    · apply Finset.prod_congr rfl
      intro j hj
      have := X7hk_hook_rem lam hc (r, j)
      have hj' := Finset.mem_range.mp hj
      simp only [hj', and_self, if_true, lt_irrefl, false_and, and_false, true_and, if_false, zero_add, add_zero] at this
      have : (hook lam (r, j) : ℚ) = hook (X7hk_rem lam (r, s) hc) (r, j) + 1 := by
        exact_mod_cast (by omega : hook lam (r, j) = hook (X7hk_rem lam (r, s) hc) (r, j) + 1)
      rw [this]; ring
    · apply Finset.prod_congr rfl
      rintro ⟨a, b⟩ hz
      have hz' := (Finset.mem_filter.mp hz).2
      have := X7hk_hook_rem lam hc (a, b)
      simp only at hz' this
      have h1 : ¬(a < r ∧ b = s) := fun h => hz'.2 h.2
      have h2 : ¬(a = r ∧ b < s) := fun h => hz'.1 h.1
      simp only [h1, h2, if_false, add_zero] at this
      rw [this]

end QAlgorithms.Papers.Independent.Next46.P26

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem X7hk_nonzero (lam : YoungDiagram) {r s : ℕ} (hc : (r, s) ∈ corners lam) :
    (∏ i ∈ Finset.range r, ((hook lam (i, s) : ℚ) - 1)) ≠ 0 ∧
    (∏ j ∈ Finset.range s, ((hook lam (r, j) : ℚ) - 1)) ≠ 0 ∧
    (∏ z ∈ (lam.cells.erase (r, s)).filter (fun z => z.1 ≠ r ∧ z.2 ≠ s), (hook lam z : ℚ)) ≠ 0 ∧
    (∏ i ∈ Finset.range r, (hook lam (i, s) : ℚ)) ≠ 0 ∧
    (∏ j ∈ Finset.range s, (hook lam (r, j) : ℚ)) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [Finset.prod_ne_zero_iff]
  · intro i hi
    have := (X7hk_col hc (Finset.mem_range.mp hi)).1
    have : (2:ℚ) ≤ hook lam (i, s) := by exact_mod_cast this
    linarith
  · intro j hj
    have := (X7hk_row hc (Finset.mem_range.mp hj)).1
    have : (2:ℚ) ≤ hook lam (r, j) := by exact_mod_cast this
    linarith
  all_goals
    intro z _
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp (X7hk_hook_ge lam _))

theorem X7hk_branching (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    ((lam.card.factorial : ℚ) / hookProduct lam =
      ∑ mu ∈ oneBoxPredecessors lam, ((lam.card - 1).factorial : ℚ) / hookProduct mu) ∧
    ((∑ mu ∈ oneBoxPredecessors lam,
      (((lam.card - 1).factorial : ℚ) / (lam.card.factorial : ℚ)) *
        (hookProduct lam / hookProduct mu)) = 1) ∧
    ((∑ z ∈ corners lam, (1 / (lam.card : ℚ)) *
      (∏ i ∈ Finset.range z.1,
        (hook lam (i, z.2) : ℚ) / ((hook lam (i, z.2) : ℚ) - 1)) *
      ∏ j ∈ Finset.range z.2,
        (hook lam (z.1, j) : ℚ) / ((hook lam (z.1, j) : ℚ) - 1)) = 1) ∧
    ((lam.card : ℚ) * (∏ z ∈ noncorners lam, ((hook lam z : ℚ) - 1)) =
      ∑ z ∈ corners lam,
        (∏ i ∈ Finset.range z.1, (hook lam (i, z.2) : ℚ)) *
        (∏ j ∈ Finset.range z.2, (hook lam (z.1, j) : ℚ)) *
        ∏ u ∈ offCross lam z.1 z.2, ((hook lam u : ℚ) - 1)) := by
  have h3 := X7hk_clause3 lam hne
  obtain ⟨m, hm⟩ : ∃ m, lam.card = m + 1 :=
    ⟨lam.card - 1, by have := Finset.card_pos.mpr hne; unfold YoungDiagram.card; omega⟩
  refine ⟨?_, ?_, h3, X7hk_clause4 lam hne⟩
  · have e : (lam.card.factorial : ℚ) / hookProduct lam =
        (lam.card.factorial : ℚ) / hookProduct lam *
          ∑ z ∈ corners lam, (1 / (lam.card : ℚ)) *
            (∏ i ∈ Finset.range z.1,
              (hook lam (i, z.2) : ℚ) / ((hook lam (i, z.2) : ℚ) - 1)) *
            ∏ j ∈ Finset.range z.2,
              (hook lam (z.1, j) : ℚ) / ((hook lam (z.1, j) : ℚ) - 1) := by
      rw [h3, mul_one]
    rw [e, Finset.mul_sum, X7hk_sum_preds, ← Finset.sum_attach]
    apply Finset.sum_congr rfl
    rintro ⟨⟨r, s⟩, hc⟩ -
    dsimp only
    obtain ⟨hl, hmu⟩ := X7hk_hookProducts lam hc
    obtain ⟨n1, n2, n3, n4, n5⟩ := X7hk_nonzero lam hc
    rw [hl, hmu, Finset.prod_div_distrib, Finset.prod_div_distrib, hm, Nat.add_sub_cancel,
      Nat.factorial_succ]
    push_cast
    field_simp
  · refine Eq.trans ?_ (Eq.trans (Finset.sum_attach _ _) h3)
    rw [X7hk_sum_preds]
    apply Finset.sum_congr rfl
    rintro ⟨⟨r, s⟩, hc⟩ -
    dsimp only
    obtain ⟨hl, hmu⟩ := X7hk_hookProducts lam hc
    obtain ⟨n1, n2, n3, n4, n5⟩ := X7hk_nonzero lam hc
    rw [hl, hmu, Finset.prod_div_distrib, Finset.prod_div_distrib, hm, Nat.add_sub_cancel,
      Nat.factorial_succ]
    push_cast
    field_simp

end QAlgorithms.Papers.Independent.Next46.P26

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem X7hk_walk_oneW (lam : YoungDiagram) (x y : ℕ → ℝ) (hp : PositiveWeights lam x y) :
    ∀ (fuel : ℕ) (z : Cell), z ∈ lam.cells →
      lam.colLen 0 + lam.rowLen 0 ≤ fuel + z.1 + z.2 + 2 →
      ∀ E : List Cell → ℝ, (∀ l c, c ∈ corners lam → E (l ++ [c]) = 1) →
        walkEval (successors lam) x y fuel z E = 1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro z hz hf E hE
    have hs : successors lam z = ∅ := by
      ext t
      simp only [successors, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro ht h
      have := X7hk_mem_lam (lam := lam) ht
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    simp only [walkEval, hs, if_true]
    simpa using hE [] z (X7hk_succ_empty hz hs)
  | succ n ih =>
    intro z hz hf E hE
    simp only [walkEval]
    split_ifs with h
    · simpa using hE [] z (X7hk_succ_empty hz h)
    · have hne : (successors lam z).Nonempty := Finset.nonempty_iff_ne_empty.mpr h
      have hw : ∀ t ∈ successors lam z, 0 < moveWeight x y z t := by
        intro t ht
        simp only [successors, Finset.mem_filter] at ht
        have := X7hk_mem_lam (lam := lam) ht.1
        unfold moveWeight
        split_ifs
        · exact hp.1 _ this.1
        · exact hp.2 _ this.2
      have hS : 0 < ∑ u ∈ successors lam z, moveWeight x y z u := Finset.sum_pos hw hne
      have key : ∀ t ∈ successors lam z,
          walkEval (successors lam) x y n t (fun tail => E (z :: tail)) = 1 := by
        intro t ht
        simp only [successors, Finset.mem_filter] at ht
        apply ih t ht.1
        · rcases ht.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        · intro l c hc
          simpa using hE (z :: l) c hc
      rw [Finset.sum_congr rfl (fun t ht => by rw [key t ht, mul_one]), ← Finset.sum_div]
      exact div_self hS.ne'

theorem X7hk_W_pos (lam : YoungDiagram) (hne : lam.cells.Nonempty) (x y : ℕ → ℝ)
    (hp : PositiveWeights lam x y) : 0 < totalWeight lam x y := by
  unfold totalWeight
  apply Finset.sum_pos _ hne
  intro z hz
  have := X7hk_mem_lam (lam := lam) hz
  exact mul_pos (hp.1 _ this.1) (hp.2 _ this.2)

theorem X7hk_totalW (lam : YoungDiagram) (hne : lam.cells.Nonempty) (x y : ℕ → ℝ)
    (hp : PositiveWeights lam x y) :
    ∑ c ∈ corners lam, terminalProb lam (successors lam) x y c = 1 := by
  unfold terminalProb
  rw [Finset.sum_comm]
  have hW := X7hk_W_pos lam hne x y hp
  have : ∀ z ∈ lam.cells,
      ∑ c ∈ corners lam, (x z.1 * y z.2 / totalWeight lam x y) *
        walkEval (successors lam) x y lam.card z
          (fun p => if p.getLast? = some c then 1 else 0) = x z.1 * y z.2 / totalWeight lam x y := by
    intro z hz
    rw [← Finset.mul_sum, ← X7hk_walk_sum, X7hk_walk_oneW lam x y hp lam.card z hz, mul_one]
    · have := X7hk_card_bound lam; omega
    · intro l c hc
      simp [Finset.sum_ite_eq', hc]
  rw [Finset.sum_congr rfl this, ← Finset.sum_div]
  exact div_self hW.ne'

/-- The weighted identity (4), for an arbitrary commutative ring. -/
def X7hk_WId {K : Type*} [CommRing K] (lam : YoungDiagram) (x y : ℕ → K) : Prop :=
  totalWeight lam x y * (∏ z ∈ noncorners lam, strictHook lam x y z.1 z.2) =
    ∑ z ∈ corners lam, x z.1 * y z.2 *
      (∏ u ∈ offCross lam z.1 z.2, strictHook lam x y u.1 u.2) *
      (∏ i ∈ Finset.range z.1, (x i + rowGap lam x y i z.1 z.2)) *
      ∏ j ∈ Finset.range z.2, (y j + colGap lam x y j z.1 z.2)

theorem X7hk_WId_map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (hf : Function.Injective f) (lam : YoungDiagram) (x y : ℕ → K)
    (h : X7hk_WId lam (fun i => f (x i)) (fun j => f (y j))) : X7hk_WId lam x y := by
  unfold X7hk_WId at h ⊢
  apply hf
  simpa [map_sum, map_prod, map_mul, map_add, strictHook, rowGap, colGap, totalWeight] using h

theorem X7hk_WId_real (lam : YoungDiagram) (x y : ℕ → ℝ) (hp : PositiveWeights lam x y) :
    X7hk_WId lam x y := by
  rcases Finset.eq_empty_or_nonempty lam.cells with h0 | hne
  · unfold X7hk_WId
    have hc : corners lam = ∅ := by simp [corners, h0]
    simp [totalWeight, h0, hc]
  have hW := X7hk_W_pos lam hne x y hp
  have htot := X7hk_totalW lam hne x y hp
  unfold X7hk_WId
  have e : totalWeight lam x y * (∏ z ∈ noncorners lam, strictHook lam x y z.1 z.2) =
      totalWeight lam x y * (∏ z ∈ noncorners lam, strictHook lam x y z.1 z.2) *
        ∑ c ∈ corners lam, terminalProb lam (successors lam) x y c := by
    rw [htot, mul_one]
  rw [e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨r, s⟩ hc
  dsimp only
  rw [weightedHookWalk lam hne x y hp (r, s) hc]
  obtain ⟨hm, hcol, hrow⟩ := X7hk_corner hc
  obtain ⟨hA, hB, hT⟩ := X7hk_noncorner_cross hc
  rw [X7hk_prod_cross _ r s (fun z => strictHook lam x y z.1 z.2) hA hB hT]
  simp only [offCross]
  have hrg : ∀ i ∈ Finset.range r, rowGap lam x y i r s = strictHook lam x y i s := by
    intro i _
    simp only [rowGap, strictHook, hcol]
  have hcg : ∀ j ∈ Finset.range s, colGap lam x y j r s = strictHook lam x y r j := by
    intro j _
    simp only [colGap, strictHook, hrow]
  have hLc : ∀ i ∈ Finset.range r, 0 < strictHook lam x y i s := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    unfold strictHook
    apply add_pos_of_pos_of_nonneg
    · apply Finset.sum_pos
      · intro k hk
        have := (Finset.mem_Ico.mp hk).2
        exact hp.1 _ (lt_of_lt_of_le this (lam.colLen_anti 0 s (Nat.zero_le _)))
      · exact ⟨r, Finset.mem_Ico.mpr ⟨hi', by omega⟩⟩
    · apply Finset.sum_nonneg
      intro l hl
      have := (Finset.mem_Ico.mp hl).2
      exact (hp.2 _ (lt_of_lt_of_le this (lam.rowLen_anti 0 i (Nat.zero_le _)))).le
  have hLr : ∀ j ∈ Finset.range s, 0 < strictHook lam x y r j := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    unfold strictHook
    apply add_pos_of_nonneg_of_pos
    · apply Finset.sum_nonneg
      intro k hk
      have := (Finset.mem_Ico.mp hk).2
      exact (hp.1 _ (lt_of_lt_of_le this (lam.colLen_anti 0 j (Nat.zero_le _)))).le
    · apply Finset.sum_pos
      · intro l hl
        have := (Finset.mem_Ico.mp hl).2
        exact hp.2 _ (lt_of_lt_of_le this (lam.rowLen_anti 0 r (Nat.zero_le _)))
      · exact ⟨s, Finset.mem_Ico.mpr ⟨hj', by omega⟩⟩
  have hP : (∏ i ∈ Finset.range r, (1 + x i / rowGap lam x y i r s)) *
      ∏ i ∈ Finset.range r, strictHook lam x y i s =
      ∏ i ∈ Finset.range r, (x i + rowGap lam x y i r s) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hrg i hi]
    have := (hLc i hi).ne'
    field_simp
    ring
  have hQ : (∏ j ∈ Finset.range s, (1 + y j / colGap lam x y j r s)) *
      ∏ j ∈ Finset.range s, strictHook lam x y r j =
      ∏ j ∈ Finset.range s, (y j + colGap lam x y j r s) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    rw [hcg j hj]
    have := (hLr j hj).ne'
    field_simp
    ring
  simp only [cornerWeight]
  rw [← hP, ← hQ]
  field_simp

end QAlgorithms.Papers.Independent.Next46.P26

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

def X7hk_cons (t : ℝ) (y : ℕ → ℝ) : ℕ → ℝ := fun j => if j = 0 then t else y (j - 1)

@[simp] theorem X7hk_cons_zero (t : ℝ) (y : ℕ → ℝ) : X7hk_cons t y 0 = t := by simp [X7hk_cons]

@[simp] theorem X7hk_cons_succ (t : ℝ) (y : ℕ → ℝ) (j : ℕ) : X7hk_cons t y (j + 1) = y j := by
  simp [X7hk_cons]

theorem X7hk_eq_of_lt_iff {a b : ℕ} (H : ∀ i, i < a ↔ i < b) : a = b :=
  le_antisymm (Nat.le_of_not_lt fun h => lt_irrefl b ((H b).mp h))
    (Nat.le_of_not_lt fun h => lt_irrefl a ((H a).mpr h))

theorem X7hk_mem_corners {lam : YoungDiagram} {z : Cell} :
    z ∈ corners lam ↔ z ∈ lam ∧ (z.1 + 1, z.2) ∉ lam ∧ (z.1, z.2 + 1) ∉ lam := by
  simp [corners]

theorem X7hk_ne_pos {lam : YoungDiagram} (hne : lam.cells.Nonempty) :
    0 < lam.colLen 0 ∧ 0 < lam.rowLen 0 := by
  obtain ⟨z, hz⟩ := hne
  have h0 : ((0 : ℕ), (0 : ℕ)) ∈ lam :=
    lam.isLowerSet (show ((0 : ℕ), (0 : ℕ)) ≤ z from ⟨Nat.zero_le _, Nat.zero_le _⟩) hz
  exact ⟨YoungDiagram.mem_iff_lt_colLen.mp h0, YoungDiagram.mem_iff_lt_rowLen.mp h0⟩

/-! ### Adding a new first column -/

def X7hk_colAug (lam : YoungDiagram) : YoungDiagram where
  cells := lam.cells.image (fun z => (z.1, z.2 + 1)) ∪
    (Finset.range (lam.colLen 0)).image (fun i => (i, 0))
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe,
      Finset.mem_range] at ha ⊢
    obtain ⟨hb1, hb2⟩ := hba
    rcases b with ⟨b1, b2⟩
    rcases ha with ⟨z, hz, rfl⟩ | ⟨i, hi, rfl⟩
    · cases b2 with
      | zero =>
        right
        refine ⟨b1, ?_, rfl⟩
        have : (b1, 0) ∈ lam := lam.isLowerSet (show (b1, 0) ≤ z from ⟨hb1, Nat.zero_le _⟩) hz
        exact YoungDiagram.mem_iff_lt_colLen.mp this
      | succ b2 =>
        left
        refine ⟨(b1, b2), ?_, rfl⟩
        exact lam.isLowerSet (show (b1, b2) ≤ z from ⟨hb1, by simp at hb2; omega⟩) hz
    · right
      simp at hb1 hb2
      exact ⟨b1, by omega, by simp [hb2]⟩

theorem X7hk_mem_colAug_zero (lam : YoungDiagram) (i : ℕ) :
    (i, 0) ∈ X7hk_colAug lam ↔ i < lam.colLen 0 := by
  show (i, 0) ∈ (X7hk_colAug lam).cells ↔ _
  simp [X7hk_colAug]

theorem X7hk_mem_colAug_succ (lam : YoungDiagram) (i j : ℕ) :
    (i, j + 1) ∈ X7hk_colAug lam ↔ (i, j) ∈ lam := by
  show (i, j + 1) ∈ (X7hk_colAug lam).cells ↔ _
  simp [X7hk_colAug]

theorem X7hk_colAug_colLen_zero (lam : YoungDiagram) :
    (X7hk_colAug lam).colLen 0 = lam.colLen 0 :=
  X7hk_eq_of_lt_iff fun i => by
    rw [← YoungDiagram.mem_iff_lt_colLen, X7hk_mem_colAug_zero]

theorem X7hk_colAug_colLen_succ (lam : YoungDiagram) (j : ℕ) :
    (X7hk_colAug lam).colLen (j + 1) = lam.colLen j :=
  X7hk_eq_of_lt_iff fun i => by
    rw [← YoungDiagram.mem_iff_lt_colLen, X7hk_mem_colAug_succ, YoungDiagram.mem_iff_lt_colLen]

theorem X7hk_colAug_rowLen (lam : YoungDiagram) {i : ℕ} (hi : i < lam.colLen 0) :
    (X7hk_colAug lam).rowLen i = lam.rowLen i + 1 :=
  X7hk_eq_of_lt_iff fun j => by
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    cases j with
    | zero => rw [X7hk_mem_colAug_zero]; simp [hi]
    | succ j => rw [X7hk_mem_colAug_succ, YoungDiagram.mem_iff_lt_rowLen]; omega

theorem X7hk_colAug_corners (lam : YoungDiagram) :
    corners (X7hk_colAug lam) = (corners lam).image (fun c => (c.1, c.2 + 1)) := by
  ext ⟨a, b⟩
  rw [X7hk_mem_corners, Finset.mem_image]
  cases b with
  | zero =>
    simp only [X7hk_mem_colAug_zero, zero_add, X7hk_mem_colAug_succ]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact absurd (YoungDiagram.mem_iff_lt_colLen.mpr h1) h3
    · rintro ⟨c, -, hc⟩
      simp at hc
  | succ b =>
    simp only [X7hk_mem_colAug_succ]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(a, b), X7hk_mem_corners.mpr ⟨h1, h2, h3⟩, rfl⟩
    · rintro ⟨⟨c1, c2⟩, hc, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, hb⟩ := he
      have hb' : c2 = b := by omega
      subst hb'
      exact X7hk_mem_corners.mp hc

theorem X7hk_colAug_W (lam : YoungDiagram) (x y : ℕ → ℝ) (t : ℝ) :
    totalWeight (X7hk_colAug lam) x (X7hk_cons t y) =
      totalWeight lam x y + t * ∑ i ∈ Finset.range (lam.colLen 0), x i := by
  unfold totalWeight
  show ∑ z ∈ (X7hk_colAug lam).cells, _ = _
  simp only [X7hk_colAug]
  rw [Finset.sum_union, Finset.sum_image (fun a _ b _ h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 (by omega)),
    Finset.sum_image (fun a _ b _ h => by simpa using h)]
  · simp [Finset.mul_sum, mul_comm]
  · rw [Finset.disjoint_left]
    intro a h1 h2
    simp only [Finset.mem_image] at h1 h2
    obtain ⟨z, -, rfl⟩ := h1
    obtain ⟨i, -, he⟩ := h2
    simp at he

theorem X7hk_corner_lt {lam : YoungDiagram} {r s : ℕ} (hc : (r, s) ∈ corners lam) :
    r < lam.colLen 0 ∧ s < lam.rowLen 0 := X7hk_mem_lam (X7hk_corner hc).1

theorem X7hk_colAug_cW (lam : YoungDiagram) (x y : ℕ → ℝ) (t : ℝ) {r s : ℕ}
    (hc : (r, s) ∈ corners lam) :
    cornerWeight (X7hk_colAug lam) x (X7hk_cons t y) r (s + 1) =
      cornerWeight lam x y r s * (1 + t / outsideA lam x y r s) := by
  have hr := (X7hk_corner_lt hc).1
  unfold cornerWeight
  rw [X7hk_cons_succ, Finset.prod_range_succ']
  have e1 : ∀ i ∈ Finset.range r, rowGap (X7hk_colAug lam) x (X7hk_cons t y) i r (s + 1) =
      rowGap lam x y i r s := by
    intro i hi
    have hi' : i < lam.colLen 0 := by have := Finset.mem_range.mp hi; omega
    unfold rowGap
    rw [X7hk_colAug_rowLen lam hi', ← Finset.sum_Ico_add' (X7hk_cons t y) (s + 1) (lam.rowLen i) 1]
    simp
  have e2 : ∀ j ∈ Finset.range s, colGap (X7hk_colAug lam) x (X7hk_cons t y) (j + 1) r (s + 1) =
      colGap lam x y j r s := by
    intro j _
    unfold colGap
    rw [X7hk_colAug_colLen_succ, ← Finset.sum_Ico_add' (X7hk_cons t y) (j + 1) (s + 1) 1]
    simp
  have e3 : colGap (X7hk_colAug lam) x (X7hk_cons t y) 0 r (s + 1) = outsideA lam x y r s := by
    unfold colGap outsideA
    rw [X7hk_colAug_colLen_zero, ← Finset.sum_Ico_add' (X7hk_cons t y) 0 (s + 1) 1,
      Finset.range_eq_Ico]
    simp
  have p1 : ∏ i ∈ Finset.range r,
      (1 + x i / rowGap (X7hk_colAug lam) x (X7hk_cons t y) i r (s + 1)) =
      ∏ i ∈ Finset.range r, (1 + x i / rowGap lam x y i r s) :=
    Finset.prod_congr rfl (fun i hi => by rw [e1 i hi])
  have p2 : ∏ j ∈ Finset.range s,
      (1 + X7hk_cons t y (j + 1) / colGap (X7hk_colAug lam) x (X7hk_cons t y) (j + 1) r (s + 1)) =
      ∏ j ∈ Finset.range s, (1 + y j / colGap lam x y j r s) :=
    Finset.prod_congr rfl (fun j hj => by rw [X7hk_cons_succ, e2 j hj])
  rw [p1, p2, X7hk_cons_zero, e3]
  ring

/-! ### Adding a new first row -/

def X7hk_rowAug (lam : YoungDiagram) : YoungDiagram where
  cells := lam.cells.image (fun z => (z.1 + 1, z.2)) ∪
    (Finset.range (lam.rowLen 0)).image (fun j => (0, j))
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe,
      Finset.mem_range] at ha ⊢
    obtain ⟨hb1, hb2⟩ := hba
    rcases b with ⟨b1, b2⟩
    rcases ha with ⟨z, hz, rfl⟩ | ⟨j, hj, rfl⟩
    · cases b1 with
      | zero =>
        right
        refine ⟨b2, ?_, rfl⟩
        have : (0, b2) ∈ lam := lam.isLowerSet (show (0, b2) ≤ z from ⟨Nat.zero_le _, hb2⟩) hz
        exact YoungDiagram.mem_iff_lt_rowLen.mp this
      | succ b1 =>
        left
        refine ⟨(b1, b2), ?_, rfl⟩
        exact lam.isLowerSet (show (b1, b2) ≤ z from ⟨by simp at hb1; omega, hb2⟩) hz
    · right
      simp at hb1 hb2
      exact ⟨b2, by omega, by simp [hb1]⟩

theorem X7hk_mem_rowAug_zero (lam : YoungDiagram) (j : ℕ) :
    (0, j) ∈ X7hk_rowAug lam ↔ j < lam.rowLen 0 := by
  show (0, j) ∈ (X7hk_rowAug lam).cells ↔ _
  simp [X7hk_rowAug]

theorem X7hk_mem_rowAug_succ (lam : YoungDiagram) (i j : ℕ) :
    (i + 1, j) ∈ X7hk_rowAug lam ↔ (i, j) ∈ lam := by
  show (i + 1, j) ∈ (X7hk_rowAug lam).cells ↔ _
  simp [X7hk_rowAug]

theorem X7hk_rowAug_rowLen_zero (lam : YoungDiagram) :
    (X7hk_rowAug lam).rowLen 0 = lam.rowLen 0 :=
  X7hk_eq_of_lt_iff fun j => by
    rw [← YoungDiagram.mem_iff_lt_rowLen, X7hk_mem_rowAug_zero]

theorem X7hk_rowAug_rowLen_succ (lam : YoungDiagram) (i : ℕ) :
    (X7hk_rowAug lam).rowLen (i + 1) = lam.rowLen i :=
  X7hk_eq_of_lt_iff fun j => by
    rw [← YoungDiagram.mem_iff_lt_rowLen, X7hk_mem_rowAug_succ, YoungDiagram.mem_iff_lt_rowLen]

theorem X7hk_rowAug_colLen (lam : YoungDiagram) {j : ℕ} (hj : j < lam.rowLen 0) :
    (X7hk_rowAug lam).colLen j = lam.colLen j + 1 :=
  X7hk_eq_of_lt_iff fun i => by
    rw [← YoungDiagram.mem_iff_lt_colLen]
    cases i with
    | zero => rw [X7hk_mem_rowAug_zero]; simp [hj]
    | succ i => rw [X7hk_mem_rowAug_succ, YoungDiagram.mem_iff_lt_colLen]; omega

theorem X7hk_rowAug_corners (lam : YoungDiagram) :
    corners (X7hk_rowAug lam) = (corners lam).image (fun c => (c.1 + 1, c.2)) := by
  ext ⟨a, b⟩
  rw [X7hk_mem_corners, Finset.mem_image]
  cases a with
  | zero =>
    simp only [X7hk_mem_rowAug_zero, zero_add, X7hk_mem_rowAug_succ]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact absurd (YoungDiagram.mem_iff_lt_rowLen.mpr h1) h2
    · rintro ⟨c, -, hc⟩
      simp at hc
  | succ a =>
    simp only [X7hk_mem_rowAug_succ]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(a, b), X7hk_mem_corners.mpr ⟨h1, h2, h3⟩, rfl⟩
    · rintro ⟨⟨c1, c2⟩, hc, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨ha, rfl⟩ := he
      have ha' : c1 = a := by omega
      subst ha'
      exact X7hk_mem_corners.mp hc

theorem X7hk_rowAug_W (lam : YoungDiagram) (x y : ℕ → ℝ) (u : ℝ) :
    totalWeight (X7hk_rowAug lam) (X7hk_cons u x) y =
      totalWeight lam x y + u * ∑ j ∈ Finset.range (lam.rowLen 0), y j := by
  unfold totalWeight
  show ∑ z ∈ (X7hk_rowAug lam).cells, _ = _
  simp only [X7hk_rowAug]
  rw [Finset.sum_union, Finset.sum_image (fun a _ b _ h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext (by omega) h.2),
    Finset.sum_image (fun a _ b _ h => by simpa using h)]
  · simp [Finset.mul_sum]
  · rw [Finset.disjoint_left]
    intro a h1 h2
    simp only [Finset.mem_image] at h1 h2
    obtain ⟨z, -, rfl⟩ := h1
    obtain ⟨i, -, he⟩ := h2
    simp at he

theorem X7hk_rowAug_cW (lam : YoungDiagram) (x y : ℕ → ℝ) (u : ℝ) {r s : ℕ}
    (hc : (r, s) ∈ corners lam) :
    cornerWeight (X7hk_rowAug lam) (X7hk_cons u x) y (r + 1) s =
      cornerWeight lam x y r s * (1 + u / outsideB lam x y r s) := by
  have hs := (X7hk_corner_lt hc).2
  unfold cornerWeight
  rw [X7hk_cons_succ, Finset.prod_range_succ']
  have e1 : ∀ i ∈ Finset.range r, rowGap (X7hk_rowAug lam) (X7hk_cons u x) y (i + 1) (r + 1) s =
      rowGap lam x y i r s := by
    intro i _
    unfold rowGap
    rw [X7hk_rowAug_rowLen_succ, ← Finset.sum_Ico_add' (X7hk_cons u x) (i + 1) (r + 1) 1]
    simp
  have e2 : ∀ j ∈ Finset.range s, colGap (X7hk_rowAug lam) (X7hk_cons u x) y j (r + 1) s =
      colGap lam x y j r s := by
    intro j hj
    have hj' : j < lam.rowLen 0 := by have := Finset.mem_range.mp hj; omega
    unfold colGap
    rw [X7hk_rowAug_colLen lam hj', ← Finset.sum_Ico_add' (X7hk_cons u x) (r + 1) (lam.colLen j) 1]
    simp
  have e3 : rowGap (X7hk_rowAug lam) (X7hk_cons u x) y 0 (r + 1) s = outsideB lam x y r s := by
    unfold rowGap outsideB
    rw [X7hk_rowAug_rowLen_zero, ← Finset.sum_Ico_add' (X7hk_cons u x) 0 (r + 1) 1,
      Finset.range_eq_Ico]
    simp
  have p1 : ∏ i ∈ Finset.range r,
      (1 + X7hk_cons u x (i + 1) / rowGap (X7hk_rowAug lam) (X7hk_cons u x) y (i + 1) (r + 1) s) =
      ∏ i ∈ Finset.range r, (1 + x i / rowGap lam x y i r s) :=
    Finset.prod_congr rfl (fun i hi => by rw [X7hk_cons_succ, e1 i hi])
  have p2 : ∏ j ∈ Finset.range s,
      (1 + y j / colGap (X7hk_rowAug lam) (X7hk_cons u x) y j (r + 1) s) =
      ∏ j ∈ Finset.range s, (1 + y j / colGap lam x y j r s) :=
    Finset.prod_congr rfl (fun j hj => by rw [e2 j hj])
  rw [p1, p2, X7hk_cons_zero, e3]
  ring

theorem X7hk_rowAug_A (lam : YoungDiagram) (hne : lam.cells.Nonempty) (x y : ℕ → ℝ) (u : ℝ)
    (r s : ℕ) :
    outsideA (X7hk_rowAug lam) (X7hk_cons u x) y (r + 1) s = outsideA lam x y r s := by
  unfold outsideA
  rw [X7hk_rowAug_colLen lam (X7hk_ne_pos hne).2,
    ← Finset.sum_Ico_add' (X7hk_cons u x) (r + 1) (lam.colLen 0) 1]
  simp

/-! ### Real identities -/

theorem X7hk_ra (lam : YoungDiagram) (hne : lam.cells.Nonempty) (x y : ℕ → ℝ)
    (hp : PositiveWeights lam x y) :
    ∑ z ∈ corners lam, cornerWeight lam x y z.1 z.2 = totalWeight lam x y := by
  have hW := X7hk_W_pos lam hne x y hp
  have h := X7hk_totalW lam hne x y hp
  rw [Finset.sum_congr rfl (fun c hc => weightedHookWalk lam hne x y hp c hc), ← Finset.sum_div,
    div_eq_one_iff_eq hW.ne'] at h
  exact h

theorem X7hk_colAug_ne (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    (X7hk_colAug lam).cells.Nonempty :=
  ⟨(0, 0), by
    show (0, 0) ∈ X7hk_colAug lam
    rw [X7hk_mem_colAug_zero]; exact (X7hk_ne_pos hne).1⟩

theorem X7hk_rowAug_ne (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    (X7hk_rowAug lam).cells.Nonempty :=
  ⟨(0, 0), by
    show (0, 0) ∈ X7hk_rowAug lam
    rw [X7hk_mem_rowAug_zero]; exact (X7hk_ne_pos hne).2⟩

theorem X7hk_colAug_pos (lam : YoungDiagram) (hne : lam.cells.Nonempty) (x y : ℕ → ℝ)
    (hp : PositiveWeights lam x y) :
    PositiveWeights (X7hk_colAug lam) x (X7hk_cons 1 y) := by
  constructor
  · intro i hi
    rw [X7hk_colAug_colLen_zero] at hi
    exact hp.1 i hi
  · intro j hj
    rw [X7hk_colAug_rowLen lam (X7hk_ne_pos hne).1] at hj
    cases j with
    | zero => simp
    | succ j => rw [X7hk_cons_succ]; exact hp.2 j (by omega)

theorem X7hk_rowAug_pos (lam : YoungDiagram) (hne : lam.cells.Nonempty) (x y : ℕ → ℝ)
    (hp : PositiveWeights lam x y) :
    PositiveWeights (X7hk_rowAug lam) (X7hk_cons 1 x) y := by
  constructor
  · intro i hi
    rw [X7hk_rowAug_colLen lam (X7hk_ne_pos hne).2] at hi
    cases i with
    | zero => simp
    | succ i => rw [X7hk_cons_succ]; exact hp.1 i (by omega)
  · intro j hj
    rw [X7hk_rowAug_rowLen_zero] at hj
    exact hp.2 j hj

theorem X7hk_rb (lam : YoungDiagram) (hne : lam.cells.Nonempty) (x y : ℕ → ℝ)
    (hp : PositiveWeights lam x y) :
    ∑ z ∈ corners lam, cornerWeight lam x y z.1 z.2 / outsideA lam x y z.1 z.2 =
      ∑ i ∈ Finset.range (lam.colLen 0), x i := by
  have h1 := X7hk_ra (X7hk_colAug lam) (X7hk_colAug_ne lam hne) x (X7hk_cons 1 y)
    (X7hk_colAug_pos lam hne x y hp)
  rw [X7hk_colAug_corners, Finset.sum_image (fun a _ b _ h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 (by omega)), X7hk_colAug_W] at h1
  rw [Finset.sum_congr rfl (fun c hc => X7hk_colAug_cW lam x y 1 hc)] at h1
  have h0 := X7hk_ra lam hne x y hp
  simp only [mul_add, mul_one, Finset.sum_add_distrib, one_mul] at h1
  simp only [mul_one_div] at h1
  linarith

theorem X7hk_rc (lam : YoungDiagram) (hne : lam.cells.Nonempty) (x y : ℕ → ℝ)
    (hp : PositiveWeights lam x y) :
    ∑ z ∈ corners lam, cornerWeight lam x y z.1 z.2 / outsideB lam x y z.1 z.2 =
      ∑ j ∈ Finset.range (lam.rowLen 0), y j := by
  have h1 := X7hk_ra (X7hk_rowAug lam) (X7hk_rowAug_ne lam hne) (X7hk_cons 1 x) y
    (X7hk_rowAug_pos lam hne x y hp)
  rw [X7hk_rowAug_corners, Finset.sum_image (fun a _ b _ h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext (by omega) h.2), X7hk_rowAug_W] at h1
  rw [Finset.sum_congr rfl (fun c hc => X7hk_rowAug_cW lam x y 1 hc)] at h1
  have h0 := X7hk_ra lam hne x y hp
  simp only [mul_add, mul_one, Finset.sum_add_distrib, one_mul] at h1
  simp only [mul_one_div] at h1
  linarith

theorem X7hk_rd (lam : YoungDiagram) (hne : lam.cells.Nonempty) (x y : ℕ → ℝ)
    (hp : PositiveWeights lam x y) :
    ∑ z ∈ corners lam, cornerWeight lam x y z.1 z.2 /
      (outsideA lam x y z.1 z.2 * outsideB lam x y z.1 z.2) = 1 := by
  have h1 := X7hk_rb (X7hk_rowAug lam) (X7hk_rowAug_ne lam hne) (X7hk_cons 1 x) y
    (X7hk_rowAug_pos lam hne x y hp)
  rw [X7hk_rowAug_corners, Finset.sum_image (fun a _ b _ h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext (by omega) h.2),
    X7hk_rowAug_colLen lam (X7hk_ne_pos hne).2, Finset.sum_range_succ'] at h1
  rw [Finset.sum_congr rfl (fun c hc => by
    rw [X7hk_rowAug_cW lam x y 1 hc, X7hk_rowAug_A lam hne]), X7hk_cons_zero] at h1
  simp only [X7hk_cons_succ] at h1
  have h0 := X7hk_rb lam hne x y hp
  have e : ∀ c ∈ corners lam, cornerWeight lam x y c.1 c.2 * (1 + 1 / outsideB lam x y c.1 c.2) /
      outsideA lam x y c.1 c.2 = cornerWeight lam x y c.1 c.2 / outsideA lam x y c.1 c.2 +
        cornerWeight lam x y c.1 c.2 / (outsideA lam x y c.1 c.2 * outsideB lam x y c.1 c.2) := by
    intro c _; ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib] at h1
  linarith

end QAlgorithms.Papers.Independent.Next46.P26

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Gen

variable {K : Type*} [CommRing K]

def X7hk_N (lam : YoungDiagram) (x y : ℕ → K) (r s : ℕ) : K :=
  x r * y s * (∏ i ∈ Finset.range r, (rowGap lam x y i r s + x i)) *
    ∏ j ∈ Finset.range s, (colGap lam x y j r s + y j)

def X7hk_D (lam : YoungDiagram) (x y : ℕ → K) (r s : ℕ) : K :=
  (∏ i ∈ Finset.range r, rowGap lam x y i r s) * ∏ j ∈ Finset.range s, colGap lam x y j r s

def X7hk_E (α β : Bool) (lam : YoungDiagram) (x y : ℕ → K) (r s : ℕ) : K :=
  X7hk_D lam x y r s * (if α then outsideA lam x y r s else 1) *
    (if β then outsideB lam x y r s else 1)

def X7hk_R (α β : Bool) (lam : YoungDiagram) (x y : ℕ → K) : K :=
  if α then (if β then 1 else ∑ i ∈ Finset.range (lam.colLen 0), x i)
  else (if β then ∑ j ∈ Finset.range (lam.rowLen 0), y j else totalWeight lam x y)

def X7hk_ClL (α β : Bool) (lam : YoungDiagram) (x y : ℕ → K) : K :=
  ∑ c ∈ corners lam, X7hk_N lam x y c.1 c.2 *
    ∏ c' ∈ (corners lam).erase c, X7hk_E α β lam x y c'.1 c'.2

def X7hk_ClR (α β : Bool) (lam : YoungDiagram) (x y : ℕ → K) : K :=
  X7hk_R α β lam x y * ∏ c ∈ corners lam, X7hk_E α β lam x y c.1 c.2

end Gen

section Maps

variable {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (lam : YoungDiagram) (x y : ℕ → K)

theorem X7hk_rowGap_map (i r s : ℕ) :
    f (rowGap lam x y i r s) = rowGap lam (fun k => f (x k)) (fun l => f (y l)) i r s := by
  simp [rowGap, map_sum]

theorem X7hk_colGap_map (j r s : ℕ) :
    f (colGap lam x y j r s) = colGap lam (fun k => f (x k)) (fun l => f (y l)) j r s := by
  simp [colGap, map_sum]

theorem X7hk_A_map (r s : ℕ) :
    f (outsideA lam x y r s) = outsideA lam (fun k => f (x k)) (fun l => f (y l)) r s := by
  simp [outsideA, map_sum]

theorem X7hk_B_map (r s : ℕ) :
    f (outsideB lam x y r s) = outsideB lam (fun k => f (x k)) (fun l => f (y l)) r s := by
  simp [outsideB, map_sum]

theorem X7hk_N_map (r s : ℕ) :
    f (X7hk_N lam x y r s) = X7hk_N lam (fun k => f (x k)) (fun l => f (y l)) r s := by
  simp [X7hk_N, map_prod, X7hk_rowGap_map, X7hk_colGap_map]

theorem X7hk_D_map (r s : ℕ) :
    f (X7hk_D lam x y r s) = X7hk_D lam (fun k => f (x k)) (fun l => f (y l)) r s := by
  simp [X7hk_D, map_prod, X7hk_rowGap_map, X7hk_colGap_map]

theorem X7hk_E_map (α β : Bool) (r s : ℕ) :
    f (X7hk_E α β lam x y r s) = X7hk_E α β lam (fun k => f (x k)) (fun l => f (y l)) r s := by
  cases α <;> cases β <;> simp [X7hk_E, X7hk_D_map, X7hk_A_map, X7hk_B_map]

theorem X7hk_R_map (α β : Bool) :
    f (X7hk_R α β lam x y) = X7hk_R α β lam (fun k => f (x k)) (fun l => f (y l)) := by
  cases α <;> cases β <;> simp [X7hk_R, map_sum, totalWeight]

theorem X7hk_ClL_map (α β : Bool) :
    f (X7hk_ClL α β lam x y) = X7hk_ClL α β lam (fun k => f (x k)) (fun l => f (y l)) := by
  simp [X7hk_ClL, map_sum, map_prod, X7hk_N_map, X7hk_E_map]

theorem X7hk_ClR_map (α β : Bool) :
    f (X7hk_ClR α β lam x y) = X7hk_ClR α β lam (fun k => f (x k)) (fun l => f (y l)) := by
  simp [X7hk_ClR, map_prod, X7hk_R_map, X7hk_E_map]

end Maps

theorem X7hk_clear {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] (C : Finset ι) (N E : ι → F) (R : F)
    (hE : ∀ c ∈ C, E c ≠ 0) :
    (∑ c ∈ C, N c / E c = R) ↔
      (∑ c ∈ C, N c * ∏ c' ∈ C.erase c, E c') = R * ∏ c ∈ C, E c := by
  have hP : ∏ c ∈ C, E c ≠ 0 := Finset.prod_ne_zero_iff.mpr hE
  have : ∑ c ∈ C, N c * ∏ c' ∈ C.erase c, E c' = (∑ c ∈ C, N c / E c) * ∏ c ∈ C, E c := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c hc
    rw [← Finset.mul_prod_erase C E hc]
    field_simp [hE c hc]
  rw [this]
  constructor
  · intro h; rw [h]
  · intro h; exact mul_right_cancel₀ hP h

theorem X7hk_term {F : Type*} [Field F] (lam : YoungDiagram) (x y : ℕ → F) (r s : ℕ)
    (hg : ∀ i ∈ Finset.range r, rowGap lam x y i r s ≠ 0)
    (hh : ∀ j ∈ Finset.range s, colGap lam x y j r s ≠ 0) (α β : Bool) :
    X7hk_N lam x y r s / X7hk_E α β lam x y r s =
      cornerWeight lam x y r s / ((if α then outsideA lam x y r s else 1) *
        (if β then outsideB lam x y r s else 1)) := by
  have h1 : ∏ i ∈ Finset.range r, (1 + x i / rowGap lam x y i r s) =
      (∏ i ∈ Finset.range r, (rowGap lam x y i r s + x i)) /
        ∏ i ∈ Finset.range r, rowGap lam x y i r s := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    field_simp [hg i hi]
  have h2 : ∏ j ∈ Finset.range s, (1 + y j / colGap lam x y j r s) =
      (∏ j ∈ Finset.range s, (colGap lam x y j r s + y j)) /
        ∏ j ∈ Finset.range s, colGap lam x y j r s := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    field_simp [hh j hj]
  unfold cornerWeight X7hk_N X7hk_E X7hk_D
  rw [h1, h2]
  field_simp

/-- Positivity of all denominators at a corner, for positive weights. -/
theorem X7hk_den_pos (lam : YoungDiagram) (x y : ℕ → ℝ) (hp : PositiveWeights lam x y)
    {r s : ℕ} (hc : (r, s) ∈ corners lam) :
    (∀ i ∈ Finset.range r, 0 < rowGap lam x y i r s) ∧
    (∀ j ∈ Finset.range s, 0 < colGap lam x y j r s) ∧
    0 < outsideA lam x y r s ∧ 0 < outsideB lam x y r s := by
  obtain ⟨hrl, hsl⟩ := X7hk_corner_lt hc
  have hx : ∀ k, k ≤ r → 0 < x k := fun k hk => hp.1 k (by omega)
  have hy : ∀ l, l ≤ s → 0 < y l := fun l hl => hp.2 l (by omega)
  have hxn : ∀ (a b : ℕ), b ≤ lam.colLen 0 → 0 ≤ ∑ k ∈ Finset.Ico a b, x k := by
    intro a b hb
    apply Finset.sum_nonneg
    intro k hk
    exact (hp.1 k (by have := (Finset.mem_Ico.mp hk).2; omega)).le
  have hyn : ∀ (a b : ℕ), b ≤ lam.rowLen 0 → 0 ≤ ∑ l ∈ Finset.Ico a b, y l := by
    intro a b hb
    apply Finset.sum_nonneg
    intro l hl
    exact (hp.2 l (by have := (Finset.mem_Ico.mp hl).2; omega)).le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    unfold rowGap
    apply add_pos_of_pos_of_nonneg
    · apply Finset.sum_pos (fun k hk => hx k (by have := (Finset.mem_Ico.mp hk).2; omega))
      exact ⟨r, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩
    · exact hyn _ _ (lam.rowLen_anti 0 i (Nat.zero_le _))
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    unfold colGap
    apply add_pos_of_nonneg_of_pos
    · exact hxn _ _ (lam.colLen_anti 0 j (Nat.zero_le _))
    · apply Finset.sum_pos (fun l hl => hy l (by have := (Finset.mem_Ico.mp hl).2; omega))
      exact ⟨s, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩
  · unfold outsideA
    apply add_pos_of_nonneg_of_pos (hxn _ _ le_rfl)
    rw [Finset.range_eq_Ico]
    apply Finset.sum_pos (fun l hl => hy l (by have := (Finset.mem_Ico.mp hl).2; omega))
    exact ⟨s, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩
  · unfold outsideB
    apply add_pos_of_pos_of_nonneg _ (hyn _ _ le_rfl)
    rw [Finset.range_eq_Ico]
    apply Finset.sum_pos (fun k hk => hx k (by have := (Finset.mem_Ico.mp hk).2; omega))
    exact ⟨r, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩

theorem X7hk_E_pos (lam : YoungDiagram) (x y : ℕ → ℝ) (hp : PositiveWeights lam x y)
    {r s : ℕ} (hc : (r, s) ∈ corners lam) (α β : Bool) : 0 < X7hk_E α β lam x y r s := by
  obtain ⟨h1, h2, h3, h4⟩ := X7hk_den_pos lam x y hp hc
  have hD : 0 < X7hk_D lam x y r s :=
    mul_pos (Finset.prod_pos h1) (Finset.prod_pos h2)
  unfold X7hk_E
  cases α <;> cases β <;> simp only [if_true, if_false, Bool.false_eq_true] <;> positivity

theorem X7hk_real_cl (lam : YoungDiagram) (hne : lam.cells.Nonempty) (x y : ℕ → ℝ)
    (hp : PositiveWeights lam x y) (α β : Bool) :
    X7hk_ClL α β lam x y = X7hk_ClR α β lam x y := by
  unfold X7hk_ClL X7hk_ClR
  rw [← X7hk_clear (corners lam) (fun c => X7hk_N lam x y c.1 c.2)
    (fun c => X7hk_E α β lam x y c.1 c.2) _ (fun c hc => (X7hk_E_pos lam x y hp hc α β).ne')]
  rw [Finset.sum_congr rfl (fun c hc => by
    obtain ⟨h1, h2, -, -⟩ := X7hk_den_pos lam x y hp hc
    exact X7hk_term lam x y c.1 c.2 (fun i hi => (h1 i hi).ne') (fun j hj => (h2 j hj).ne') α β)]
  cases α <;> cases β <;>
    simp only [X7hk_R, if_true, if_false, Bool.false_eq_true, mul_one, one_mul, div_one]
  · exact X7hk_ra lam hne x y hp
  · exact X7hk_rc lam hne x y hp
  · exact X7hk_rb lam hne x y hp
  · exact X7hk_rd lam hne x y hp

/-- Positivity of evaluations of the formal variables. -/
theorem X7hk_eval_pos (lam : YoungDiagram) (v : Sum (Fin (lam.colLen 0)) (Fin (lam.rowLen 0)) → ℚ)
    (hv : ∀ a, 0 < v a) :
    PositiveWeights lam (fun i => ((Rat.castHom ℝ).comp (MvPolynomial.eval v)) (polyX lam i))
      (fun j => ((Rat.castHom ℝ).comp (MvPolynomial.eval v)) (polyY lam j)) := by
  constructor
  · intro i hi
    simp only [RingHom.comp_apply, polyX, dif_pos hi, MvPolynomial.eval_X]
    rw [Rat.coe_castHom]; exact_mod_cast hv _
  · intro j hj
    simp only [RingHom.comp_apply, polyY, dif_pos hj, MvPolynomial.eval_X]
    rw [Rat.coe_castHom]; exact_mod_cast hv _

theorem X7hk_poly_cl (lam : YoungDiagram) (hne : lam.cells.Nonempty) (α β : Bool) :
    X7hk_ClL α β lam (polyX lam) (polyY lam) = X7hk_ClR α β lam (polyX lam) (polyY lam) := by
  apply MvPolynomial.funext_set (fun _ => Set.Ioi (0:ℚ)) (fun _ => Set.Ioi_infinite 0)
  intro v hv
  have hv' : ∀ a, 0 < v a := fun a => hv a (Set.mem_univ a)
  let f : WeightPoly lam →+* ℝ := (Rat.castHom ℝ).comp (MvPolynomial.eval v)
  have h := X7hk_real_cl lam hne _ _ (X7hk_eval_pos lam v hv') α β
  apply (Rat.cast_injective (α := ℝ))
  have e1 : ∀ p : WeightPoly lam, ((MvPolynomial.eval v p : ℚ) : ℝ) = f p := fun p => rfl
  rw [e1, e1, X7hk_ClL_map, X7hk_ClR_map]
  exact h

theorem X7hk_ne_K (lam : YoungDiagram) (p : WeightPoly lam)
    (h : ((Rat.castHom ℝ).comp (MvPolynomial.eval (fun _ => (1:ℚ)))) p ≠ 0) :
    algebraMap (WeightPoly lam) (WeightRat lam) p ≠ 0 := by
  intro h0
  apply h
  have : p = 0 := (IsFractionRing.injective (WeightPoly lam) (WeightRat lam)) (by rw [h0, map_zero])
  rw [this, map_zero]

end QAlgorithms.Papers.Independent.Next46.P26

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem X7hk_K_cl (lam : YoungDiagram) (hne : lam.cells.Nonempty) (α β : Bool) :
    X7hk_ClL α β lam (ratX lam) (ratY lam) = X7hk_ClR α β lam (ratX lam) (ratY lam) := by
  have hcl := congrArg (algebraMap (WeightPoly lam) (WeightRat lam)) (X7hk_poly_cl lam hne α β)
  rw [X7hk_ClL_map, X7hk_ClR_map] at hcl
  exact hcl

theorem X7hk_K_ne (lam : YoungDiagram) (p : WeightPoly lam) (q : ℝ)
    (hq : ((Rat.castHom ℝ).comp (MvPolynomial.eval (fun _ => (1:ℚ)))) p = q) (h : q ≠ 0) :
    algebraMap (WeightPoly lam) (WeightRat lam) p ≠ 0 :=
  X7hk_ne_K lam p (hq ▸ h)

theorem X7hk_weightedBranching (lam : YoungDiagram) (hne : lam.cells.Nonempty) (α β : Bool) :
    ∑ c ∈ corners lam, cornerWeight lam (ratX lam) (ratY lam) c.1 c.2 /
      ((if α then outsideA lam (ratX lam) (ratY lam) c.1 c.2 else 1) *
        (if β then outsideB lam (ratX lam) (ratY lam) c.1 c.2 else 1)) =
      X7hk_R α β lam (ratX lam) (ratY lam) := by
  have hp1 := X7hk_eval_pos lam (fun _ => (1:ℚ)) (fun _ => one_pos)
  have hcl := X7hk_K_cl lam hne α β
  unfold X7hk_ClL X7hk_ClR at hcl
  have hE : ∀ c ∈ corners lam, X7hk_E α β lam (ratX lam) (ratY lam) c.1 c.2 ≠ 0 := by
    intro c hc
    rw [show X7hk_E α β lam (ratX lam) (ratY lam) c.1 c.2 = algebraMap _ _
      (X7hk_E α β lam (polyX lam) (polyY lam) c.1 c.2) from (X7hk_E_map _ lam _ _ α β c.1 c.2).symm]
    exact X7hk_K_ne lam _ _ (X7hk_E_map _ lam (polyX lam) (polyY lam) α β c.1 c.2)
      (X7hk_E_pos lam _ _ hp1 hc α β).ne'
  have hcl' := (X7hk_clear (corners lam) (fun c => X7hk_N lam (ratX lam) (ratY lam) c.1 c.2)
    (fun c => X7hk_E α β lam (ratX lam) (ratY lam) c.1 c.2) (X7hk_R α β lam (ratX lam) (ratY lam))
    hE).mpr hcl
  refine Eq.trans ?_ hcl'
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨h1, h2, -, -⟩ := X7hk_den_pos lam _ _ hp1 hc
  rw [X7hk_term]
  · intro i hi
    rw [show rowGap lam (ratX lam) (ratY lam) i c.1 c.2 = algebraMap _ _
      (rowGap lam (polyX lam) (polyY lam) i c.1 c.2) from (X7hk_rowGap_map _ lam _ _ i c.1 c.2).symm]
    exact X7hk_K_ne lam _ _ (X7hk_rowGap_map _ lam (polyX lam) (polyY lam) i c.1 c.2) (h1 i hi).ne'
  · intro j hj
    rw [show colGap lam (ratX lam) (ratY lam) j c.1 c.2 = algebraMap _ _
      (colGap lam (polyX lam) (polyY lam) j c.1 c.2) from (X7hk_colGap_map _ lam _ _ j c.1 c.2).symm]
    exact X7hk_K_ne lam _ _ (X7hk_colGap_map _ lam (polyX lam) (polyY lam) j c.1 c.2) (h2 j hj).ne'

end QAlgorithms.Papers.Independent.Next46.P26

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem X7hk_WB (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    ((∑ z ∈ corners lam, cornerWeight lam (ratX lam) (ratY lam) z.1 z.2) =
      totalWeight lam (ratX lam) (ratY lam)) ∧
    ((∑ z ∈ corners lam, cornerWeight lam (ratX lam) (ratY lam) z.1 z.2 /
      outsideA lam (ratX lam) (ratY lam) z.1 z.2) =
      ∑ i ∈ Finset.range (lam.colLen 0), ratX lam i) ∧
    ((∑ z ∈ corners lam, cornerWeight lam (ratX lam) (ratY lam) z.1 z.2 /
      outsideB lam (ratX lam) (ratY lam) z.1 z.2) =
      ∑ j ∈ Finset.range (lam.rowLen 0), ratY lam j) ∧
    ((∑ z ∈ corners lam, cornerWeight lam (ratX lam) (ratY lam) z.1 z.2 /
      (outsideA lam (ratX lam) (ratY lam) z.1 z.2 *
        outsideB lam (ratX lam) (ratY lam) z.1 z.2)) = 1) := by
  have a := X7hk_weightedBranching lam hne false false
  have b := X7hk_weightedBranching lam hne true false
  have c := X7hk_weightedBranching lam hne false true
  have d := X7hk_weightedBranching lam hne true true
  simp only [X7hk_R, if_true, if_false, Bool.false_eq_true, mul_one, one_mul, div_one] at a b c d
  exact ⟨a, b, c, d⟩

end QAlgorithms.Papers.Independent.Next46.P26

end

open QAlgorithms.Papers.Independent.Next46.P26 in
theorem solution (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    ((∑ z ∈ corners lam, cornerWeight lam (ratX lam) (ratY lam) z.1 z.2) =
      totalWeight lam (ratX lam) (ratY lam)) ∧
    ((∑ z ∈ corners lam, cornerWeight lam (ratX lam) (ratY lam) z.1 z.2 /
      outsideA lam (ratX lam) (ratY lam) z.1 z.2) =
      ∑ i ∈ Finset.range (lam.colLen 0), ratX lam i) ∧
    ((∑ z ∈ corners lam, cornerWeight lam (ratX lam) (ratY lam) z.1 z.2 /
      outsideB lam (ratX lam) (ratY lam) z.1 z.2) =
      ∑ j ∈ Finset.range (lam.rowLen 0), ratY lam j) ∧
    ((∑ z ∈ corners lam, cornerWeight lam (ratX lam) (ratY lam) z.1 z.2 /
      (outsideA lam (ratX lam) (ratY lam) z.1 z.2 *
        outsideB lam (ratX lam) (ratY lam) z.1 z.2)) = 1) :=
  QAlgorithms.Papers.Independent.Next46.P26.X7hk_WB lam hne
