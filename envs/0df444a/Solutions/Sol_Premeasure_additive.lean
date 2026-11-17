-- Prove2me | solution 1 for Premeasure.additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:45:12.410543+00:00
-- url     : https://prove2.me/submissions/d668c2b3-a06f-4b8c-8fd7-97cd326a9f36

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F000
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Tactic


/-!
# Pre-measure on a Field of Sets

This module defines a "field of sets" (also known as an algebra of sets) and the concept
of a "pre-measure" defined on such a field, as per the provided definition.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set ENNReal Function MeasureTheory

namespace FieldOfSets

end FieldOfSets

section Premeasure
open Premeasure

variable {Ω : Type*} {F₀ : FieldOfSets Ω}


/-- Union of the two-set support family used in finite additivity. -/
private theorem source_two_set_iUnion {Ω : Type*} (s t : Set Ω) :
    (⋃ i : ℕ, if i = 0 then s else if i = 1 then t else ∅) = s ∪ t := by
  let A : ℕ → Set Ω := fun i => if i = 0 then s else if i = 1 then t else ∅
  change (⋃ i, A i) = s ∪ t
  ext x
  simp only [mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    rcases i with (_ | _ | i) <;> simp_all [A]
  · intro hx
    exact hx.elim (fun hxs => ⟨0, by simpa [A] using hxs⟩)
      (fun hxt => ⟨1, by simpa [A] using hxt⟩)

/-- Pairwise disjointness of the two-set support family. -/
private theorem source_two_set_pairwise {Ω : Type*} (s t : Set Ω) (hst : Disjoint s t) :
    Pairwise (Disjoint on (fun i : ℕ => if i = 0 then s else if i = 1 then t else ∅)) := by
  let A : ℕ → Set Ω := fun i => if i = 0 then s else if i = 1 then t else ∅
  change Pairwise (Disjoint on A)
  intro i j hij
  rcases i with (_ | _ | i) <;> rcases j with (_ | _ | j) <;>
    simp_all [A, Function.onFun, hst.symm]

theorem solution (pm : Premeasure F₀) {s t : Set Ω}
    (hs : s ∈ F₀.carrier) (ht : t ∈ F₀.carrier) (hst : Disjoint s t)
    (hut : s ∪ t ∈ F₀.carrier) :
    pm.μ₀ ⟨s ∪ t, hut⟩ = pm.μ₀ ⟨s, hs⟩ + pm.μ₀ ⟨t, ht⟩ := by
  let A : ℕ → Set Ω := fun i => if i = 0 then s else if i = 1 then t else ∅
  have hA : ∀ i, A i ∈ F₀.carrier := by
    intro i
    rcases i with (_ | _ | i) <;> simp [A, hs, ht, F₀.empty_mem]
  have hUset : (⋃ i, A i) = s ∪ t := source_two_set_iUnion s t
  have hU : (⋃ i, A i) ∈ F₀.carrier := hUset ▸ hut
  have hdisj : Pairwise (Disjoint on A) := source_two_set_pairwise s t hst
  have hsigma := pm.sigma_additive A hA hU hdisj
  calc
    pm.μ₀ ⟨s ∪ t, hut⟩ = pm.μ₀ ⟨⋃ i, A i, hU⟩ :=
      congrArg pm.μ₀ (Subtype.ext hUset.symm)
    _ = ∑' i, pm.μ₀ ⟨A i, hA i⟩ := hsigma
    _ = pm.μ₀ ⟨s, hs⟩ + pm.μ₀ ⟨t, ht⟩ := by
      rw [tsum_eq_sum (s := Finset.range 2)]
      · simp [A, Finset.sum_range_succ]
      · intro j hj
        simp only [Finset.mem_range, not_lt] at hj
        have hj0 : j ≠ 0 := by omega
        have hj1 : j ≠ 1 := by omega
        simpa [A, hj0, hj1] using pm.map_empty
end Premeasure
