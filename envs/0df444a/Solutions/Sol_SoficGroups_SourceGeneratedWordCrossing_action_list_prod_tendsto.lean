-- Prove2me | solution 1 for SoficGroups.SourceGeneratedWordCrossing.action_list_prod_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/c457047b-0d94-4349-9e08-9187b97efd3b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_nonneg
import Theorems.Thm_SoficGroups_normalizedHamming_triangle
import Theorems.Thm_SoficGroups_normalizedHamming_mul_left

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceGeneratedWordCrossing
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceGeneratedWordCrossing
theorem _root_.solution
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G) (l : List G) :
    Tendsto
      (fun n =>
        SoficGroups.normalizedHamming
          ((A.model n).action l.prod)
          ((l.map (A.model n).action).prod))
      atTop (nhds 0) := by
  induction l with
  | nil =>
      simp [SoficGroups.PermutationModel.map_one,
        SoficGroups.normalizedHamming_self]
  | cons g l ih =>
      simp only [List.map_cons, List.prod_cons]
      have hupper : Tendsto
          (fun n =>
            SoficGroups.normalizedHamming
                ((A.model n).action (g * l.prod))
                ((A.model n).action g * (A.model n).action l.prod) +
              SoficGroups.normalizedHamming
                ((A.model n).action l.prod)
                ((l.map (A.model n).action).prod))
          atTop (nhds 0) := by
        simpa using (A.multiplicative g l.prod).add ih
      refine squeeze_zero
        (fun n => SoficGroups.normalizedHamming_nonneg _ _) ?_ hupper
      intro n
      have htriangle := SoficGroups.normalizedHamming_triangle
        ((A.model n).action (g * l.prod))
        ((A.model n).action g * (A.model n).action l.prod)
        ((A.model n).action g *
          (l.map (A.model n).action).prod)
      rw [SoficGroups.normalizedHamming_mul_left] at htriangle
      exact htriangle
end SoficGroups.SourceGeneratedWordCrossing
