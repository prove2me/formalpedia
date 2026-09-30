-- Prove2me | solution 1 for SP4RankNine.finite_graded_cancellation_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-08T02:02:00.00191+00:00
-- url     : https://prove2.me/submissions/a7413269-01c3-4f4c-9f17-4d276d1b235b

import Definitions.Def_SP4RankNine

set_option autoImplicit false

/-!
# Finite cancellation rigidity underlying the rank-nine geography argument

This is newly authored finite graded-pairing mathematics from the corrected
rank-nine source note, Section 2. It does not define knot Floer homology or
assert that an arbitrary knot supplies the pairing data below.
-/

namespace SP4RankNineProof

open SP4RankNine

open scoped BigOperators

def sign (b : Bool) : ℤ := if b then 1 else -1

theorem paired_degree_identity {α : Type*} {A M : α → ℤ}
    (P : CancellationPairing A M) (i : α) :
    sign (P.source i) * M i + sign (P.source (P.mate i)) * M (P.mate i) = 1 := by
  have he := P.exchange i
  cases hi : P.source i
  · have hm : P.source (P.mate i) = true := by simpa [hi] using he
    have hd := P.degree (P.mate i) hm
    rw [P.involutive i] at hd
    simp [sign, hm]
    omega
  · have hm : P.source (P.mate i) = false := by simpa [hi] using he
    have hd := P.degree i hi
    simp [sign, hm]
    omega

theorem degree_balance {A M : Fin 8 → ℤ} (P : CancellationPairing A M) :
    (∑ i, sign (P.source i) * M i) = 4 := by
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => paired_degree_identity P i)
  rw [Finset.sum_add_distrib] at hs
  have hp := P.mate.sum_comp (fun i => sign (P.source i) * M i)
  rw [hp] at hs
  norm_num at hs
  omega

theorem source_count {A M : Fin 8 → ℤ} (P : CancellationPairing A M) :
    (∑ i, (if P.source i then (1 : ℤ) else 0)) = 4 := by
  have hpoint (i : Fin 8) :
      (if P.source i then (1 : ℤ) else 0) +
        (if P.source (P.mate i) then (1 : ℤ) else 0) = 1 := by
    rw [P.exchange]
    cases P.source i <;> decide
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => hpoint i)
  rw [Finset.sum_add_distrib] at hs
  have hp := P.mate.sum_comp (fun i => if P.source i then (1 : ℤ) else 0)
  rw [hp] at hs
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  omega

theorem source_of_max {α : Type*} {A M : α → ℤ}
    (P : CancellationPairing A M) (i : α) (hi : ∀ j, A j ≤ A i) :
    P.source i = true := by
  cases hs : P.source i
  · have hm : P.source (P.mate i) = true := by simpa [hs] using P.exchange i
    have hl := P.lower (P.mate i) hm
    rw [P.involutive i] at hl
    have hh := hi (P.mate i)
    omega
  · rfl

theorem target_of_min {α : Type*} {A M : α → ℤ}
    (P : CancellationPairing A M) (i : α) (hi : ∀ j, A i ≤ A j) :
    P.source i = false := by
  cases hs : P.source i
  · rfl
  · have hl := P.lower i hs
    have hh := hi (P.mate i)
    omega

/-- The five-level pairing has exactly the `F` source pattern, and its
intermediate height is forced to be one below its top height. -/
theorem five_level_source_rigidity
    (g h a b c d : ℤ) (hh : 0 < h) (hgh : h < g)
    (hparity : c % 2 ≠ d % 2)
    (P : CancellationPairing (fiveLevel g h) (fiveMaslov g h a b c d)) :
    h = g - 1 ∧
      P.source = ![true, true, false, false, true, true, false, false] := by
  have h0 : P.source 0 = true := by
    apply source_of_max
    intro j
    fin_cases j <;> simp [fiveLevel] <;> omega
  have h1 : P.source 1 = true := by
    apply source_of_max
    intro j
    fin_cases j <;> simp [fiveLevel] <;> omega
  have h6 : P.source 6 = false := by
    apply target_of_min
    intro j
    fin_cases j <;> simp [fiveLevel] <;> omega
  have h7 : P.source 7 = false := by
    apply target_of_min
    intro j
    fin_cases j <;> simp [fiveLevel] <;> omega
  have hb := degree_balance P
  have hc := source_count P
  simp only [Fin.sum_univ_succ] at hc
  have hmid : h = g - 1 ∧ P.source 2 = false ∧ P.source 3 = false ∧
      P.source 4 = true ∧ P.source 5 = true := by
    cases h2 : P.source 2 <;> cases h3 : P.source 3 <;>
      cases h4 : P.source 4 <;> cases h5 : P.source 5 <;>
      simp [Fin.sum_univ_succ, sign, fiveMaslov, h0, h1, h2, h3, h4, h5, h6, h7] at hb hc ⊢ <;>
      omega
  refine ⟨hmid.1, ?_⟩
  funext i
  fin_cases i <;> simp [h0, h1, hmid.2.1, hmid.2.2.1, hmid.2.2.2.1, hmid.2.2.2.2, h6, h7]

/-- The actual partners, not just their source labels, follow the two
rank-two channels: top to positive intermediate and negative intermediate
to bottom. -/
theorem five_level_pairing_rigidity
    (g h a b c d : ℤ) (hh : 0 < h) (hgh : h < g)
    (hparity : c % 2 ≠ d % 2)
    (P : CancellationPairing (fiveLevel g h) (fiveMaslov g h a b c d)) :
    h = g - 1 ∧
      P.source = ![true, true, false, false, true, true, false, false] ∧
      (∀ i : Fin 8, i.val < 2 → 2 ≤ (P.mate i).val ∧ (P.mate i).val < 4) ∧
      (∀ i : Fin 8, 4 ≤ i.val → i.val < 6 → 6 ≤ (P.mate i).val) := by
  obtain ⟨hgap, hsrc⟩ := five_level_source_rigidity g h a b c d hh hgh hparity P
  have hupper (j : Fin 8) : h < fiveLevel g h j → j.val < 2 := by
    fin_cases j <;> simp [fiveLevel] <;> omega
  have hlower (j : Fin 8) : fiveLevel g h j < -h → 6 ≤ j.val := by
    fin_cases j <;> simp [fiveLevel] <;> omega
  have ht2 : (P.mate 2).val < 2 := by
    apply hupper
    have hm : P.source (P.mate 2) = true := by simp [P.exchange, hsrc]
    have hl := P.lower (P.mate 2) hm
    rw [P.involutive 2] at hl
    simpa [fiveLevel] using hl
  have ht3 : (P.mate 3).val < 2 := by
    apply hupper
    have hm : P.source (P.mate 3) = true := by simp [P.exchange, hsrc]
    have hl := P.lower (P.mate 3) hm
    rw [P.involutive 3] at hl
    simpa [fiveLevel] using hl
  have htwo : P.mate 2 = 0 ∨ P.mate 2 = 1 := by
    have hv : (P.mate 2).val = 0 ∨ (P.mate 2).val = 1 := by omega
    exact hv.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  have hthree : P.mate 3 = 0 ∨ P.mate 3 = 1 := by
    have hv : (P.mate 3).val = 0 ∨ (P.mate 3).val = 1 := by omega
    exact hv.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  have hne : P.mate 2 ≠ P.mate 3 := P.mate.injective.ne (by decide)
  have htop : ∀ i : Fin 8, i.val < 2 → 2 ≤ (P.mate i).val ∧ (P.mate i).val < 4 := by
    have h0 := P.involutive 2
    have h1 := P.involutive 3
    rcases htwo with htwo | htwo <;> rcases hthree with hthree | hthree
    · exact False.elim (hne (htwo.trans hthree.symm))
    · rw [htwo] at h0
      rw [hthree] at h1
      intro i hi
      fin_cases i <;> simp_all
    · rw [htwo] at h0
      rw [hthree] at h1
      intro i hi
      fin_cases i <;> simp_all
    · exact False.elim (hne (htwo.trans hthree.symm))
  refine ⟨hgap, hsrc, htop, ?_⟩
  intro i hi hj
  have hs : P.source i = true := by
    fin_cases i <;> simp_all
  have hl := P.lower i hs
  have ha : fiveLevel g h i = -h := by
    fin_cases i <;> simp_all [fiveLevel]
  rw [ha] at hl
  exact hlower (P.mate i) hl

/-- Conjugation and degree-one cancellation exclude four top and four
bottom atoms with no other nonpermanent atom. -/
theorem four_one_four_impossible
    (g a b c d : ℤ) (hg : 0 < g) :
    ¬ Nonempty (CancellationPairing (fourFourLevel g) (fourFourMaslov g a b c d)) := by
  rintro ⟨P⟩
  have hsource (i : Fin 8) (hi : i.val < 4) : P.source i = true := by
    apply source_of_max
    intro j
    fin_cases i <;> fin_cases j <;> simp_all [fourFourLevel] <;> omega
  have htarget (i : Fin 8) (hi : 4 ≤ i.val) : P.source i = false := by
    apply target_of_min
    intro j
    fin_cases i <;> fin_cases j <;> simp_all [fourFourLevel] <;> omega
  have hs : P.source = ![true, true, true, true, false, false, false, false] := by
    funext i
    fin_cases i
    · exact hsource 0 (by decide)
    · exact hsource 1 (by decide)
    · exact hsource 2 (by decide)
    · exact hsource 3 (by decide)
    · exact htarget 4 (by decide)
    · exact htarget 5 (by decide)
    · exact htarget 6 (by decide)
    · exact htarget 7 (by decide)
  have hb := degree_balance P
  simp [Fin.sum_univ_succ, sign, fourFourMaslov, hs] at hb
  omega

end SP4RankNineProof

open SP4RankNine

/-- The finite arithmetic and pairing layer, without a knot-Floer bridge. -/
theorem solution :
    (∀ g a b c d : ℤ, 0 < g →
      ¬ Nonempty (CancellationPairing (fourFourLevel g) (fourFourMaslov g a b c d))) ∧
    (∀ g h a b c d : ℤ, 0 < h → h < g → c % 2 ≠ d % 2 →
      ∀ P : CancellationPairing (fiveLevel g h) (fiveMaslov g h a b c d),
        h = g - 1 ∧
          P.source = ![true, true, false, false, true, true, false, false] ∧
          (∀ i : Fin 8, i.val < 2 →
            2 ≤ (P.mate i).val ∧ (P.mate i).val < 4) ∧
          (∀ i : Fin 8, 4 ≤ i.val → i.val < 6 → 6 ≤ (P.mate i).val)) := by
  constructor
  · exact SP4RankNineProof.four_one_four_impossible
  · exact SP4RankNineProof.five_level_pairing_rigidity

