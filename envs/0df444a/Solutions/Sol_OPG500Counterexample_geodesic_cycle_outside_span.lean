-- Prove2me | solution 1 for OPG500Counterexample.geodesic_cycle_outside_span
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T15:21:26.892611+00:00
-- url     : https://prove2.me/submissions/1999ff24-a0c3-4171-8d82-350a8908fd39

import Definitions.Def_opg500_weighted_cycle_models

open Set
open scoped Sym2

universe u

open OPG500Counterexample in
/-- A graph-level finite descent principle: a shortest cycle outside a closed
family is geodesic. -/
theorem solution
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ℓ : EdgeWeight G) (hpositive : IsPositive ℓ)
    (inside : (Sym2 V → ZMod 2) → Prop)
    (inside_add : ∀ a b, inside a → inside b → inside (a + b))
    (table : List (Cycle G))
    (complete : ∀ C : Cycle G, C ∈ table)
    (outside : ∃ C : Cycle G, ¬ inside C.edgeVector)
    (split : ∀ C : Cycle G, ¬ C.IsGeodesic ℓ →
      ∃ A B : Cycle G,
        Walk.weightedLength ℓ A.walk < Walk.weightedLength ℓ C.walk ∧
        Walk.weightedLength ℓ B.walk < Walk.weightedLength ℓ C.walk ∧
        C.edgeVector = A.edgeVector + B.edgeVector) :
    ∃ C : Cycle G, C.IsGeodesic ℓ ∧ ¬ inside C.edgeVector := by
  classical
  -- The finite set of cycles lying outside the family.
  set bad : Finset (Cycle G) :=
    table.toFinset.filter (fun C => ¬ inside C.edgeVector) with hbad
  have hmem : ∀ C : Cycle G, C ∈ bad ↔ ¬ inside C.edgeVector := by
    intro C
    simp [hbad, complete C]
  have hne : bad.Nonempty := by
    obtain ⟨C₀, hC₀⟩ := outside
    exact ⟨C₀, (hmem C₀).mpr hC₀⟩
  obtain ⟨Cm, hCmmem, hCmmin⟩ :=
    Finset.exists_min_image bad (fun C => Walk.weightedLength ℓ C.walk) hne
  have hCmbad : ¬ inside Cm.edgeVector := (hmem Cm).mp hCmmem
  refine ⟨Cm, ?_, hCmbad⟩
  by_contra hgeo
  obtain ⟨A, B, hA, hB, hsum⟩ := split Cm hgeo
  -- One of the two shorter pieces must also lie outside the family.
  have hAB : ¬ inside A.edgeVector ∨ ¬ inside B.edgeVector := by
    by_contra hcon
    push Not at hcon
    exact hCmbad (hsum ▸ inside_add _ _ hcon.1 hcon.2)
  rcases hAB with h | h
  · exact absurd (hCmmin A ((hmem A).mpr h)) (not_le.mpr hA)
  · exact absurd (hCmmin B ((hmem B).mpr h)) (not_le.mpr hB)
