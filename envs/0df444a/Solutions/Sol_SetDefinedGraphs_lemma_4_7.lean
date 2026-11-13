-- Prove2me | solution 1 for SetDefinedGraphs.lemma_4_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:21:49.615218+00:00
-- url     : https://prove2.me/submissions/4e0fd43c-52e2-432e-886c-afd219afac4c

import Mathlib
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses

section
set_option autoImplicit false
namespace SetDefinedGraphs
theorem chk_lemma_4_7 {d : ℕ} (D : FullClause (Fin d)) (hD : IsDiscreteClause D)
    (L : Finset (Fin d)) (hLD : L = loopCoords D) (hL : L ≠ Finset.univ)
    (V : Set (Fin d → ℕ)) (hV : IsInjectiveSet V) (a : L → ℕ) (ha : Function.Injective a)
    (v w : Fin d → ℕ) (hv : v ∈ sliceSet V L a) (hw : w ∈ sliceSet V L a) (hvw : v ≠ w) :
    (¬ (realisation (dnfFun {D}) (sliceSet V L a)).Adj ⟨v, hv⟩ ⟨w, hw⟩ ∧
        ¬ (realisation (dnfFun {D}) (sliceSet V L a)).Adj ⟨w, hw⟩ ⟨v, hv⟩) ↔
      ∃ i ∉ L, ∃ j ∉ L, v i = w j := by
  classical
  have hDd : ∀ i j, D i j = true ↔ (i = j ∧ i ∈ L) := by
    intro i j
    have hLmem : i ∈ L ↔ D i i = true := by rw [hLD]; simp [loopCoords]
    constructor
    · intro h
      have := hD.2 i j h
      subst this
      exact ⟨rfl, hLmem.2 h⟩
    · rintro ⟨rfl, h⟩; exact hLmem.1 h
  have hvi := hV v hv.1
  have hwi := hV w hw.1
  have key : ∀ x y : Fin d → ℕ, Function.Injective x → Function.Injective y →
      (∀ i : L, x i.1 = y i.1) →
      (eqPattern x y = D ↔ ¬ ∃ i ∉ L, ∃ j ∉ L, x i = y j) := by
    intro x y hx hy hxy
    constructor
    · intro h ⟨i, hi, j, hj, e⟩
      have := congrFun (congrFun h i) j
      have h2 : D i j = true := by rw [← this]; simpa [eqPattern] using e
      exact hi ((hDd i j).1 h2).2 |>.elim
    · intro h
      funext i j
      apply Bool.eq_iff_iff.2
      rw [hDd]
      simp only [eqPattern, decide_eq_true_eq]
      constructor
      · intro e
        by_cases hi : i ∈ L
        · have h1 := hxy ⟨i, hi⟩
          have : i = j := hy (by rw [← e]; exact h1.symm)
          exact ⟨this, hi⟩
        · by_cases hj : j ∈ L
          · have h1 := hxy ⟨j, hj⟩
            have : i = j := hx (by rw [e]; exact h1.symm)
            exact ⟨this, this ▸ hj⟩
          · exact (h ⟨i, hi, j, hj, e⟩).elim
      · rintro ⟨rfl, hi⟩
        exact hxy ⟨i, hi⟩
  have hsl : ∀ i : L, v i.1 = w i.1 := fun i => (hv.2 i).trans (hw.2 i).symm
  have hsl' : ∀ i : L, w i.1 = v i.1 := fun i => (hsl i).symm
  have e1 := key v w hvi hwi hsl
  have e2 := key w v hwi hvi hsl'
  have sym : (∃ i ∉ L, ∃ j ∉ L, w i = v j) ↔ ∃ i ∉ L, ∃ j ∉ L, v i = w j := by
    constructor
    · rintro ⟨i, hi, j, hj, e⟩; exact ⟨j, hj, i, hi, e.symm⟩
    · rintro ⟨i, hi, j, hj, e⟩; exact ⟨j, hj, i, hi, e.symm⟩
  have hvw' : (⟨v, hv⟩ : sliceSet V L a) ≠ ⟨w, hw⟩ := fun h => hvw (congrArg Subtype.val h)
  have hwv' : (⟨w, hw⟩ : sliceSet V L a) ≠ ⟨v, hv⟩ := fun h => hvw (congrArg Subtype.val h).symm
  have hA : ¬ (realisation (dnfFun {D}) (sliceSet V L a)).Adj ⟨v, hv⟩ ⟨w, hw⟩ ↔ ∃ i ∉ L, ∃ j ∉ L, v i = w j := by
    simp only [realisation, dnfFun, Finset.mem_singleton, decide_eq_true_eq, ne_eq, hvw', not_false_eq_true, true_and]
    rw [e1]; exact not_not
  have hB : ¬ (realisation (dnfFun {D}) (sliceSet V L a)).Adj ⟨w, hw⟩ ⟨v, hv⟩ ↔ ∃ i ∉ L, ∃ j ∉ L, v i = w j := by
    simp only [realisation, dnfFun, Finset.mem_singleton, decide_eq_true_eq, ne_eq, hwv', not_false_eq_true, true_and]
    rw [e2, not_not, sym]
  rw [hA, hB, and_self]
end SetDefinedGraphs
end

theorem solution : type_of% @SetDefinedGraphs.chk_lemma_4_7 := @SetDefinedGraphs.chk_lemma_4_7
