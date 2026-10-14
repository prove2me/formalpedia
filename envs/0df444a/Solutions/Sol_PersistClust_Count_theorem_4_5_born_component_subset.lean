-- Prove2me | solution 1 for PersistClust.Count.theorem_4_5_born_component_subset
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T17:17:24.686719+00:00
-- url     : https://prove2.me/submissions/bdd17070-55bc-4a8e-ab06-833041a1f977

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_FiltrationLaw

open PersistClust.Count

/- The superlevel-set filtration is a genuine FiltrationLaw: stage sets are
antitone and the joined-in relation is a compatible filtration relation. -/
theorem t45gamma_super_filtrationLaw {X : Type*} [TopologicalSpace X] (f : X → ℝ) :
    FiltrationLaw (superlevel f) (fun t => JoinedIn (superlevel f t)) where
  antitone := fun s t hst x hx => hst.trans hx
  mem := fun _ _ _ h => JoinedIn.mem h
  refl := fun _ _ hx => JoinedIn.refl hx
  symm := fun _ _ _ h => JoinedIn.symm h
  trans := fun _ _ _ _ h1 h2 => JoinedIn.trans h1 h2
  compat := fun s t hst _ _ h => JoinedIn.mono h (fun z hz => hst.trans hz)

theorem solution {X : Type*} [MetricSpace X] {f : X → ℝ} {c δ t : ℝ} (ht : c * δ < t) {x₀ y : X}
    (hy : JoinedIn (superlevel f t) x₀ y) :
    y ∈ pathComponentIn (superlevel f (c * δ)) x₀ :=
  JoinedIn.mono hy ((t45gamma_super_filtrationLaw f).antitone (le_of_lt ht))
