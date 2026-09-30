-- Prove2me | solution 1 for PhilipponMultiplicity.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-28T17:18:40.432221+00:00
-- url     : https://prove2.me/submissions/4b78bbd6-692c-4e3d-adfb-9e83b68cc474

import Theorems.Thm_PhilipponMultiplicity_section_five_differential_containment
import Theorems.Thm_PhilipponMultiplicity_section_five_counting_inequality
import Theorems.Thm_PhilipponMultiplicity_section_five_stabilizer_incomplete_definition
set_option autoImplicit false
open PhilipponMultiplicity
open scoped BigOperators

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (C : SectionFiveConstruction G A) :
    (∀ g ∈ C.samplingSet,
      differentialIdeal A g C.contactParameter C.chosenIdeal ≤ C.componentPrime) ∧
    (let H := C.stabilizer.identityComponent
      let s := analyticCodimension A H
      (Nat.choose (C.contactParameter + s) s : ℝ) *
          (cosetCount C.samplingSet H : ℝ) * hilbertDegreeForm G H C.degrees ≤
        hilbertDegreeForm G Set.univ C.scaledDegrees) ∧
    (IncompletelyDefines G
      (⨆ v : {x : G.Point // x ∈ C.component}, translatedIdeal G v.1 C.chosenIdeal)
      C.stabilizer.carrier) := by
  exact ⟨section_five_differential_containment K hK G A C,
    section_five_counting_inequality K hK G A C,
    section_five_stabilizer_incomplete_definition K hK G A C⟩
