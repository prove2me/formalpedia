-- Prove2me | solution 1 for PersistClust.Count.crit_free_descent_surjective
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T19:45:40.971562+00:00
-- url     : https://prove2.me/submissions/647cdacf-068a-4a2b-94d4-e2a9c9c8f8ff

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

theorem solution {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {w w' : ℝ} (hww : w ≤ w')
    (hfree : ∀ τ ∈ critSet hTame, τ < w ∨ w' < τ) (C : comps stage J w) :
    ∃ C' : comps stage J w', structMap hLaw hww C' = C := by
  have hx := (compRep_spec stage J w C).1
  have hdir := (critSet_spec hTame w w' hww hfree).1
  obtain ⟨y, hy, hJy⟩ := hdir (compRep stage J w C) hx
  have hprop : {z | J w' y z} ∈ (fun x => {z | J w' x z}) '' stage w' := ⟨y, hy, rfl⟩
  refine ⟨⟨{z | J w' y z}, hprop⟩, ?_⟩
  have hspecy := compRep_spec stage J w' ⟨{z | J w' y z}, hprop⟩
  have hJw'rep : J w' (compRep stage J w' ⟨{z | J w' y z}, hprop⟩) y := by
    have hmem : y ∈ ((fun x => {z | J w' x z})
        (compRep stage J w' ⟨{z | J w' y z}, hprop⟩)) := by
      rw [hspecy.2]
      exact hLaw.refl hy
    exact hmem
  have hJwrep : J w (compRep stage J w' ⟨{z | J w' y z}, hprop⟩) (compRep stage J w C) :=
    hLaw.trans (hLaw.compat hww hJw'rep) (hLaw.symm hJy)
  refine Subtype.ext ?_
  rw [structMap_val]
  rw [show C.val = ((fun x => {z | J w x z}) (compRep stage J w C)) from
    (compRep_spec stage J w C).2.symm]
  ext z
  exact ⟨fun hz => hLaw.trans (hLaw.symm hJwrep) hz, fun hz => hLaw.trans hJwrep hz⟩
