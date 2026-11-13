-- Prove2me | solution 1 for SetDefinedGraphs.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:21:50.011183+00:00
-- url     : https://prove2.me/submissions/abe05c0b-01e3-452a-bfad-212bf7d00795

import Mathlib
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses

section
set_option autoImplicit false
namespace SetDefinedGraphs.Dev.L48
theorem nonadj_iff {d : ℕ} (D : FullClause (Fin d)) (hD : IsDiscreteClause D)
    (L : Finset (Fin d)) (hLD : L = loopCoords D) (hL : L ≠ Finset.univ)
    (V : Set (Fin d → ℕ)) (hV : IsInjectiveSet V) (a : L → ℕ)
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

theorem main {d : ℕ} (D : FullClause (Fin d)) (hD : IsDiscreteClause D)
    (L : Finset (Fin d)) (hLD : L = loopCoords D) (hL : L ≠ Finset.univ)
    (V : Set (Fin d → ℕ)) (hVfin : V.Finite) (hV : IsInjectiveSet V) (a : L → ℕ) :
    ∃ R : Finset ℕ, R.card ≤ d * omega (realisation (dnfFun {D}) (sliceSet V L a)) ∧
      Lᶜ.card * R.card ≤ d ^ 2 * omega (realisation (dnfFun {D}) (sliceSet V L a)) ∧
      sliceSet V L a = ⋃ i ∈ Lᶜ, ⋃ r ∈ R, {v | v ∈ sliceSet V L a ∧ v i = r} := by
  classical
  set S := sliceSet V L a with hS
  have hSfin : S.Finite := hVfin.subset (fun v hv => hv.1)
  haveI : Finite S := hSfin.to_subtype
  letI : Fintype S := Fintype.ofFinite S
  set G := realisation (dnfFun {D}) S with hG
  set H := SimpleGraph.fromRel G.Adj with hH
  obtain ⟨K, hK⟩ := H.exists_isNClique_cliqueNum
  have hω : omega G = K.card := by rw [show omega G = H.cliqueNum from rfl, ← hK.card_eq]
  have hd : Lᶜ.card ≤ d := by
    simpa using Finset.card_le_univ (Lᶜ)
  have h2 : (∑ k ∈ K, (Lᶜ.image (fun i => k.1 i)).card) ≤ d * omega G := by
    calc _ ≤ ∑ k ∈ K, d := Finset.sum_le_sum (fun k _ => Finset.card_image_le.trans hd)
      _ = d * omega G := by simp [hω, mul_comm]
  refine ⟨K.biUnion (fun k => Lᶜ.image (fun i => k.1 i)), ?_, ?_, ?_⟩
  · exact (Finset.card_biUnion_le).trans h2
  · calc Lᶜ.card * _ ≤ d * (d * omega G) := Nat.mul_le_mul hd ((Finset.card_biUnion_le).trans h2)
      _ = d ^ 2 * omega G := by ring
  · apply Set.Subset.antisymm
    · intro v hv
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_biUnion, Finset.mem_image, exists_prop]
      by_cases hvK : (⟨v, hv⟩ : S) ∈ K
      · obtain ⟨i, hi⟩ : ∃ i, i ∈ Lᶜ := by
          by_contra hne
          push_neg at hne
          apply hL
          ext i
          simpa using hne i
        exact ⟨i, hi, v i, ⟨⟨v, hv⟩, hvK, i, hi, rfl⟩, hv, rfl⟩
      · have : ∃ k ∈ K, ¬ H.Adj ⟨v, hv⟩ k := by
          by_contra hno
          push_neg at hno
          have hcl : H.IsClique ((insert (⟨v, hv⟩ : S) K : Finset S) : Set S) := by
            rw [Finset.coe_insert, SimpleGraph.isClique_insert]
            exact ⟨hK.isClique, fun b hb _ => hno b hb⟩
          have := hcl.card_le_cliqueNum
          rw [Finset.card_insert_of_notMem hvK, hK.card_eq] at this
          omega
        obtain ⟨k, hkK, hk⟩ := this
        have hne : (⟨v, hv⟩ : S) ≠ k := fun h => hvK (h ▸ hkK)
        have hne' : v ≠ k.1 := fun h => hne (Subtype.ext h)
        rw [hH, SimpleGraph.fromRel_adj] at hk
        push_neg at hk
        have h1 := hk hne
        have hh := (nonadj_iff D hD L hLD hL V hV a v k.1 hv k.2 hne').1 (by
          refine ⟨?_, ?_⟩
          · exact h1.1
          · exact h1.2)
        obtain ⟨i, hi, j, hj, e⟩ := hh
        refine ⟨i, by simpa using hi, v i, ⟨k, hkK, j, by simpa using hj, e.symm⟩, hv, rfl⟩
    · intro v hv
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hv
      obtain ⟨i, _, r, _, h, _⟩ := hv
      exact h
end SetDefinedGraphs.Dev.L48
namespace SetDefinedGraphs
open SetDefinedGraphs.Dev.L48 in
theorem chk_lemma_4_8 {d : ℕ} (D : FullClause (Fin d)) (hD : IsDiscreteClause D)
    (L : Finset (Fin d)) (hLD : L = loopCoords D) (hL : L ≠ Finset.univ)
    (V : Set (Fin d → ℕ)) (hVfin : V.Finite) (hV : IsInjectiveSet V) (a : L → ℕ) (ha : Function.Injective a) :
    ∃ R : Finset ℕ, R.card ≤ d * omega (realisation (dnfFun {D}) (sliceSet V L a)) ∧
      Lᶜ.card * R.card ≤ d ^ 2 * omega (realisation (dnfFun {D}) (sliceSet V L a)) ∧
      sliceSet V L a = ⋃ i ∈ Lᶜ, ⋃ r ∈ R, {v | v ∈ sliceSet V L a ∧ v i = r} :=
  main D hD L hLD hL V hVfin hV a
end SetDefinedGraphs
end

theorem solution : type_of% @SetDefinedGraphs.chk_lemma_4_8 := @SetDefinedGraphs.chk_lemma_4_8
