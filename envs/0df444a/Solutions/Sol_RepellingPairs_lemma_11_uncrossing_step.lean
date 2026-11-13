-- Prove2me | solution 1 for RepellingPairs.lemma_11_uncrossing_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:33:45.528194+00:00
-- url     : https://prove2.me/submissions/92f61860-a305-4ce9-aa84-08829198f065

import Mathlib
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Definitions.Def_RepellingPairs_IsGoodPair
import Theorems.Thm_RepellingPairs_claim_12_good_pair_exists
import Theorems.Thm_RepellingPairs_claim_13_minimal_good_pair

section
set_option autoImplicit false

namespace RepellingPairs.Dev.Lemma11Geo

open RepellingPairs RepellingPairs.Config

variable {n : ℕ}

/-- The side predicate as a proposition on natural numbers. -/
def O (i j a : ℕ) : Prop := (i ≤ j ∧ i < a ∧ a ≤ j) ∨ (j < i ∧ (i < a ∨ a ≤ j))

theorem onSide_iff (i j a : Fin n) : onSide i j a = true ↔ O i j a := by
  unfold onSide O
  by_cases h : i ≤ j
  · have h1 : i.val ≤ j.val := h
    simp only [h, if_true, decide_eq_true_eq, Fin.lt_def, Fin.le_iff_val_le_val]; omega
  · have h' : j.val < i.val := by have : ¬ i.val ≤ j.val := h; omega
    simp only [h, if_false, decide_eq_true_eq, Bool.decide_or, Bool.or_eq_true, Fin.lt_def, Fin.le_iff_val_le_val]; omega

open Classical in
theorem cc_mk (i j p q : Fin n) :
    chordCross i j s(p, q) = if (O i j p ↔ O i j q) then 0 else 1 := by
  show (if onSide i j p = onSide i j q then 0 else 1) = _
  have : (onSide i j p = onSide i j q) ↔ (O i j p ↔ O i j q) := by
    rw [Bool.eq_iff_iff, onSide_iff, onSide_iff]
  simp only [this]
  
open Classical in
theorem cc_symm (i j p q : Fin n) : chordCross i j s(p, q) = chordCross j i s(p, q) := by
  rw [cc_mk, cc_mk]
  by_cases h1 : (O i j p ↔ O i j q) <;> by_cases h2 : (O j i p ↔ O j i q) <;>
    simp only [h1, h2, if_true, if_false] <;> simp only [O] at h1 h2 <;> omega

theorem cc_cases (i j p q : Fin n) :
    (chordCross i j s(p, q) = 0 ∧ (O i j p ↔ O i j q)) ∨ (chordCross i j s(p, q) = 1 ∧ ¬ (O i j p ↔ O i j q)) := by
  rw [cc_mk]
  by_cases h : (O i j p ↔ O i j q) <;> simp [h]

theorem onSide_false_iff (i j a : Fin n) : onSide i j a = false ↔ ¬ O i j a := by
  rw [← onSide_iff]; simp

theorem boc_iff (p q b : Fin n) : BarOnClockwiseSegment p q b ↔
    ((p.val ≤ q.val ∧ p.val ≤ b.val ∧ b.val < q.val) ∨ (q.val < p.val ∧ (p.val ≤ b.val ∨ b.val < q.val))) := by
  unfold BarOnClockwiseSegment
  by_cases h : p ≤ q
  · have : p.val ≤ q.val := h
    simp only [h, if_true, Fin.lt_def]; omega
  · have : q.val < p.val := by have : ¬ p.val ≤ q.val := h; omega
    simp only [h, if_false]; omega

theorem bb_iff (p q av b : Fin n) : BarBetween p q av b ↔
    (((p.val ≤ q.val ∧ p.val ≤ b.val ∧ b.val < q.val) ∨ (q.val < p.val ∧ (p.val ≤ b.val ∨ b.val < q.val))) ∧
      ¬ O p q av) ∨
    (((q.val ≤ p.val ∧ q.val ≤ b.val ∧ b.val < p.val) ∨ (p.val < q.val ∧ (q.val ≤ b.val ∨ b.val < p.val))) ∧
      ¬ O q p av) := by
  unfold BarBetween
  rw [onSide_false_iff, onSide_false_iff, boc_iff, boc_iff]

theorem geo1 (x y a b c i j : Fin n) (hcr : ChordsCross x a y b) (hds : OnDifferentSides x a y c)
    (hin : InSegment x a c b) :
    chordCross i j s(x, b) + chordCross i j s(a, y) = chordCross i j s(x, a) + chordCross i j s(y, b) ∨
    (chordCross i j s(x, b) + chordCross i j s(a, y) + 2 = chordCross i j s(x, a) + chordCross i j s(y, b) ∧
      ((BarBetween x y a i ∧ BarBetween a c x j) ∨ (BarBetween x y a j ∧ BarBetween a c x i))) := by
  rw [bb_iff, bb_iff, bb_iff, bb_iff]
  simp only [ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff] at hcr hds hin
  rcases cc_cases i j x b with h1 | h1 <;> rcases cc_cases i j a y with h2 | h2 <;>
    rcases cc_cases i j x a with h3 | h3 <;> rcases cc_cases i j y b with h4 | h4 <;>
    simp only [O] at h1 h2 h3 h4 ⊢ <;> grind (splits := 500)

end RepellingPairs.Dev.Lemma11Geo
end

section
set_option autoImplicit false

namespace RepellingPairs.Dev.Lemma11Geo2

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.Lemma11Geo

variable {n : ℕ}

set_option maxHeartbeats 4000000 in
theorem geo2 (x y a b c d i j : Fin n) (hcr : ChordsCross x a y b) (hds : OnDifferentSides x a y c)
    (hin : ¬ InSegment x a c b) (hin2 : InSegment x a c d) (hdc : d ≠ c) :
    chordCross i j s(x, b) + chordCross i j s(a, y) = chordCross i j s(x, a) + chordCross i j s(y, b) ∨
    (chordCross i j s(x, b) + chordCross i j s(a, y) + 2 = chordCross i j s(x, a) + chordCross i j s(y, b) ∧
      ((BarBetween x y a i ∧ BarBetween a c x j) ∨ (BarBetween x y a j ∧ BarBetween a c x i) ∨
       (BarBetween y x b i ∧ BarBetween b d y j) ∨ (BarBetween y x b j ∧ BarBetween b d y i))) := by
  rw [bb_iff, bb_iff, bb_iff, bb_iff, bb_iff, bb_iff, bb_iff, bb_iff]
  have h1 := cc_cases i j x b
  have h2 := cc_cases i j a y
  have h3 := cc_cases i j x a
  have h4 := cc_cases i j y b
  simp only [O] at h1 h2 h3 h4 ⊢
  rw [Ne, Fin.ext_iff] at hdc
  simp only [OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff] at hds hin hin2
  rcases hcr with hcr | hcr <;>
    simp only [CyclicallyOrdered, Fin.lt_def] at hcr <;>
    rcases hcr with hcr | hcr | hcr | hcr <;> grind (splits := 500)

end RepellingPairs.Dev.Lemma11Geo2
end

section
set_option autoImplicit false

namespace RepellingPairs.Dev.Lemma11Good

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.Lemma11Geo

variable {n : ℕ}

theorem goodyx_pure (x y a b c d : Fin n) (hcr : ChordsCross x a y b) (hds : OnDifferentSides x a y c)
    (hin : ¬ InSegment x a c b) (hin2 : InSegment x a c d) (hdy : d ≠ y) (hdx : d ≠ x) (hdc : d ≠ c) :
    ChordsCross y b x a ∧ OnDifferentSides y b x d ∧ (InSegment y b d a ∨ InSegment y b d c) := by
  rw [Ne, Fin.ext_iff] at hdy hdc hdx
  simp only [ChordsCross, OnDifferentSides, InSegment, CyclicallyOrdered, Fin.lt_def, Fin.ext_iff] at hcr hds hin hin2 ⊢
  grind (splits := 500)

theorem ne_of_cross {x a y b : Fin n} (h : ChordsCross x a y b) : x ≠ y := by
  simp only [ChordsCross, CyclicallyOrdered, Fin.lt_def] at h
  rw [Ne, Fin.ext_iff]; omega

theorem ne_of_dsides {u v p q : Fin n} (h : OnDifferentSides u v p q) : q ≠ p := by
  simp only [OnDifferentSides, CyclicallyOrdered, Fin.lt_def] at h
  rw [Ne, Fin.ext_iff]; omega

theorem good_yx {C C' : PerfectMatching n} {x y : Fin n}
    (hg : IsGoodPair C C' x y) (hin : ¬ InSegment x (C.partner x) (C'.partner x) (C.partner y))
    (hin2 : InSegment x (C.partner x) (C'.partner x) (C'.partner y)) : IsGoodPair C C' y x := by
  obtain ⟨hcr, hds, -⟩ := hg
  have hdy := C'.ne_self y
  have hdc : C'.partner y ≠ C'.partner x := fun h => ne_of_cross hcr (C'.involutive.injective h).symm
  have hdx : C'.partner y ≠ x := fun h => ne_of_dsides hds (by
    rw [← C'.involutive y, h])
  exact goodyx_pure x y _ _ _ _ hcr hds hin hin2 hdy hdx hdc

end RepellingPairs.Dev.Lemma11Good
end

section
set_option autoImplicit false

namespace RepellingPairs.Dev.Lemma11

open RepellingPairs RepellingPairs.Config RepellingPairs.Dev.Lemma11Geo RepellingPairs.Dev.Lemma11Geo2
  RepellingPairs.Dev.Lemma11Good

variable {n : ℕ}

theorem dist_symm (C : Config n) (i j : Fin n) : C.dist i j = C.dist j i := by
  unfold Config.dist
  congr 1
  apply Multiset.map_congr rfl
  intro s _
  induction s using Sym2.ind with
  | _ p q => exact cc_symm i j p q

theorem dist_two (m₁ m₂ : Sym2 (Fin n)) (rest : Config n) (i j : Fin n) :
    Config.dist (m₁ ::ₘ m₂ ::ₘ rest) i j = chordCross i j m₁ + chordCross i j m₂ + rest.dist i j := by
  unfold Config.dist
  rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
  omega

theorem distinct4 {x a y b : Fin n} (h : ChordsCross x a y b) :
    x ≠ a ∧ x ≠ y ∧ x ≠ b ∧ a ≠ y ∧ a ≠ b ∧ y ≠ b := by
  simp only [ChordsCross, CyclicallyOrdered, Fin.lt_def] at h
  simp only [ne_eq, Fin.ext_iff]
  omega

theorem segcount_symm (C : PerfectMatching n) (x y : Fin n)
    (hcr : ChordsCross x (C.partner x) y (C.partner y)) : segmentCount C y x = segmentCount C x y := by
  unfold segmentCount
  congr 1
  apply Finset.filter_congr
  intro p _
  simp only [ChordsCross, CyclicallyOrdered, Fin.lt_def] at hcr ⊢
  grind (splits := 500)

theorem config_split (C : PerfectMatching n) (x y : Fin n) (hne : s(x, C.partner x) ≠ s(y, C.partner y)) :
    ∃ rest : Config n, C.config = s(x, C.partner x) ::ₘ s(y, C.partner y) ::ₘ rest := by
  have h1 : s(x, C.partner x) ∈ C.config := by
    unfold PerfectMatching.config
    exact Finset.mem_val.mpr (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
  have h2 : s(y, C.partner y) ∈ C.config := by
    unfold PerfectMatching.config
    exact Finset.mem_val.mpr (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩)
  have h2' : s(y, C.partner y) ∈ C.config.erase s(x, C.partner x) :=
    (Multiset.mem_erase_of_ne (Ne.symm hne)).mpr h2
  refine ⟨(C.config.erase s(x, C.partner x)).erase s(y, C.partner y), ?_⟩
  rw [Multiset.cons_erase h2', Multiset.cons_erase h1]

theorem main (C C' : PerfectMatching n)
    (h : Config.StrictlyDominates C.config C'.config) :
    ∃ C₁ : Config n, Config.UncrossStep C.config C₁ ∧ Config.Dominates C₁ C'.config := by
  classical
  have hex : ∃ k, ∃ x y, IsGoodPair C C' x y ∧ segmentCount C x y = k := by
    obtain ⟨x, y, hg⟩ := claim_12_good_pair_exists C C' h
    exact ⟨_, x, y, hg, rfl⟩
  obtain ⟨x, y, hgood, hk⟩ := Nat.find_spec hex
  have hmin : ∀ x₂ y₂, IsGoodPair C C' x₂ y₂ → segmentCount C x y ≤ segmentCount C x₂ y₂ := by
    intro x₂ y₂ hg₂
    rw [hk]
    exact Nat.find_min' hex ⟨x₂, y₂, hg₂, rfl⟩
  clear hk
  obtain ⟨hcr, hds, hseg⟩ := hgood
  obtain ⟨-, hxy, hxb, hay, hab, -⟩ := distinct4 hcr
  have hne : s(x, C.partner x) ≠ s(y, C.partner y) := by
    intro he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hxy h1
    · exact hxb h1
  obtain ⟨rest, hrest⟩ := config_split C x y hne
  refine ⟨s(x, C.partner y) ::ₘ s(C.partner x, y) ::ₘ rest, ⟨x, C.partner x, y, C.partner y, rest, hcr, hrest,
    Or.inr rfl⟩, ?_⟩
  have hdist : ∀ i j, Config.dist C.config i j =
      chordCross i j s(x, C.partner x) + chordCross i j s(y, C.partner y) + rest.dist i j := by
    intro i j; rw [hrest, dist_two]
  have hdom := h.1
  intro i j
  have hd0 := hdom i j
  rw [hdist] at hd0
  rw [dist_two]
  have hgood : IsGoodPair C C' x y := ⟨hcr, hds, hseg⟩
  by_cases hin : InSegment x (C.partner x) (C'.partner x) (C.partner y)
  · rcases geo1 x y _ _ _ i j hcr hds hin with h1 | ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩
    · omega
    · have := claim_13_minimal_good_pair C C' h x y hgood hmin i j h2 h3
      rw [hdist] at this
      omega
    · have := claim_13_minimal_good_pair C C' h x y hgood hmin j i h2 h3
      rw [dist_symm C'.config j i, dist_symm C.config j i, hdist] at this
      omega
  · have hin2 : InSegment x (C.partner x) (C'.partner x) (C'.partner y) := by
      rcases hseg with h' | h'
      · exact absurd h' hin
      · exact h'
    have hgyx := good_yx hgood hin hin2
    have hdc : C'.partner y ≠ C'.partner x := fun h' => hxy (C'.involutive.injective h').symm
    have hmin' : ∀ x₂ y₂, IsGoodPair C C' x₂ y₂ → segmentCount C y x ≤ segmentCount C x₂ y₂ := by
      intro x₂ y₂ hg₂
      rw [segcount_symm C x y hcr]
      exact hmin x₂ y₂ hg₂
    rcases geo2 x y _ _ _ _ i j hcr hds hin hin2 hdc with
      h1 | ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩⟩
    · omega
    · have := claim_13_minimal_good_pair C C' h x y hgood hmin i j h2 h3
      rw [hdist] at this
      omega
    · have := claim_13_minimal_good_pair C C' h x y hgood hmin j i h2 h3
      rw [dist_symm C'.config j i, dist_symm C.config j i, hdist] at this
      omega
    · have := claim_13_minimal_good_pair C C' h y x hgyx hmin' i j h2 h3
      rw [hdist] at this
      omega
    · have := claim_13_minimal_good_pair C C' h y x hgyx hmin' j i h2 h3
      rw [dist_symm C'.config j i, dist_symm C.config j i, hdist] at this
      omega

end RepellingPairs.Dev.Lemma11

namespace RepellingPairs

theorem chk_lemma_11_uncrossing_step {n : ℕ} (C C' : PerfectMatching n)
    (h : Config.StrictlyDominates C.config C'.config) :
    ∃ C₁ : Config n, Config.UncrossStep C.config C₁ ∧ Config.Dominates C₁ C'.config :=
  Dev.Lemma11.main C C' h

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_lemma_11_uncrossing_step := @RepellingPairs.chk_lemma_11_uncrossing_step
