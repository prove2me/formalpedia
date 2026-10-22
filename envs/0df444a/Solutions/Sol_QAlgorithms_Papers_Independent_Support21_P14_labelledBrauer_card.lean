-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P14.labelledBrauer_card
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:23:32.70572+00:00
-- url     : https://prove2.me/submissions/4b41c4ed-f5a4-4878-9bfe-4a330b3c00f6

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14
noncomputable section

open scoped BigOperators Classical

open QAlgorithms.Papers.Independent.Support21.P14

/-- fiber of fixed-point-free involutions with prescribed mate of `a`. -/
def g68b_fib {α : Type} [DecidableEq α] (a b : α) (hab : b ≠ a) :
    {f : {f : α → α // Function.Involutive f ∧ ∀ i, f i ≠ i} // f.1 a = b} ≃
    {q : {x : α // x ≠ a ∧ x ≠ b} → {x : α // x ≠ a ∧ x ≠ b} //
      Function.Involutive q ∧ ∀ i, q i ≠ i} where
  toFun f := ⟨fun x => ⟨f.1.1 x.1, by
      obtain ⟨⟨g, hg, hfp⟩, hga⟩ := f
      obtain ⟨x, hxa, hxb⟩ := x
      refine ⟨fun h => hxb ?_, fun h => hxa ?_⟩
      · simp only at h hga; rw [← hg x, h, hga]
      · simp only at h hga; rw [← hg x, h, ← hga, hg a]⟩, by
      refine ⟨fun x => ?_, fun x h => ?_⟩
      · exact Subtype.ext (f.1.2.1 x.1)
      · exact f.1.2.2 x.1 (congrArg Subtype.val h)⟩
  invFun q := ⟨⟨fun x => if h : x = a then b else if h' : x = b then a else (q.1 ⟨x, h, h'⟩).1, by
      refine ⟨fun x => ?_, fun x => ?_⟩
      · by_cases h : x = a
        · subst h; simp [hab]
        · by_cases h' : x = b
          · subst h'; simp [hab, h]
          · have h1 := (q.1 ⟨x, h, h'⟩).2
            simp only [h, h', dif_neg, not_false_eq_true, h1.1, h1.2]
            rw [q.2.1]
      · by_cases h : x = a
        · subst h; simp [hab]
        · by_cases h' : x = b
          · subst h'; simp [h, Ne.symm h]
          · simp only [h, h', dif_neg, not_false_eq_true]
            intro e; exact q.2.2 ⟨x, h, h'⟩ (Subtype.ext e)⟩, by simp⟩
  left_inv f := by
    obtain ⟨⟨g, hg, hfp⟩, hga⟩ := f
    simp only at hga
    apply Subtype.ext; apply Subtype.ext; funext x
    simp only
    by_cases h : x = a
    · subst h; simp [hga]
    · by_cases h' : x = b
      · rw [dif_neg h, dif_pos h', h', ← hga, hg a]
      · simp [h, h']
  right_inv q := by
    apply Subtype.ext; funext x
    obtain ⟨x, h, h'⟩ := x
    apply Subtype.ext
    simp [h, h']

theorem g68b_count (n : ℕ) : ∀ (α : Type) [Fintype α] [DecidableEq α], Fintype.card α = 2*n →
    Nat.card {f : α → α // Function.Involutive f ∧ ∀ i, f i ≠ i} = oddPairingCount n := by
  induction n with
  | zero =>
    intro α _ _ hα
    have : IsEmpty α := Fintype.card_eq_zero_iff.mp (by simpa using hα)
    rw [Nat.card_eq_one_iff_unique.mpr ⟨⟨fun f g => Subtype.ext (funext fun x => isEmptyElim x)⟩,
      ⟨⟨isEmptyElim, fun x => isEmptyElim x, fun x => isEmptyElim x⟩⟩⟩]
    simp [oddPairingCount]
  | succ n ih =>
    intro α _ _ hα
    have hne : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨a⟩ := hne
    let g : {f : α → α // Function.Involutive f ∧ ∀ i, f i ≠ i} → {b : α // b ≠ a} :=
      fun f => ⟨f.1 a, f.2.2 a⟩
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv g), Nat.card_sigma]
    have hf : ∀ b : {b : α // b ≠ a}, Nat.card {f // g f = b} = oddPairingCount n := by
      intro b
      have e : {f // g f = b} ≃ {f : {f : α → α // Function.Involutive f ∧ ∀ i, f i ≠ i} // f.1 a = b.1} :=
        Equiv.subtypeEquivRight fun f => by simp [g, Subtype.ext_iff]
      rw [Nat.card_congr (e.trans (g68b_fib a b.1 b.2))]
      apply ih
      rw [Fintype.card_subtype]
      have : (Finset.univ.filter fun x : α => x ≠ a ∧ x ≠ b.1) = Finset.univ \ {a, b.1} := by
        ext x; simp
      rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hα,
        Finset.card_pair (Ne.symm b.2)]
      omega
    simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hα]
    simp only [oddPairingCount, Finset.prod_range_succ]
    rw [show 2 * (n+1) - 1 = 2*n+1 by omega]; ring

theorem g68b_half (n : ℕ) (p : BrauerPairing n) : Fintype.card {i // i < p.val i} = n := by
  obtain ⟨f, hf, hfp⟩ := p
  change Fintype.card {i // i < f i} = n
  rw [Fintype.card_subtype]
  have hB : (Finset.univ.filter fun i => f i < i).card = (Finset.univ.filter fun i => i < f i).card := by
    refine Finset.card_nbij' f f ?_ ?_ ?_ ?_ <;> intro i hi <;> simp_all [hf i]
  have hU : (Finset.univ.filter fun i => i < f i) ∪ (Finset.univ.filter fun i => f i < i) = Finset.univ := by
    ext i; simpa using lt_or_gt_of_ne (hfp i).symm
  have hD : Disjoint (Finset.univ.filter fun i => i < f i) (Finset.univ.filter fun i => f i < i) :=
    Finset.disjoint_filter.mpr fun i _ h1 h2 => lt_asymm h1 h2
  have := Finset.card_union_of_disjoint hD
  rw [hU, Finset.card_univ, Fintype.card_fin, hB] at this
  omega

/-- Unnumbered labelled Brauer-diagram count, §5, PDF p.43.
Includes n=0, where both the empty pairing and its empty labelling are unique. -/
theorem solution (n r : ℕ) (hr : 0 < r) :
    Nat.card (LabelledBrauerDiagram n r) = r^n * oddPairingCount n := by
  haveI : Fintype (BrauerPairing n) := by unfold BrauerPairing; infer_instance
  unfold LabelledBrauerDiagram
  rw [Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, g68b_half]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  have := g68b_count n (Fin (2*n)) (by simp)
  unfold BrauerPairing; rw [this]; ring
