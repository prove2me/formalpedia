-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.action_list_prod_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/2a68589c-2f20-48c6-b243-8b720c825e4b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_nonneg
import Theorems.Thm_SoficGroups_normalizedHamming_triangle
import Theorems.Thm_SoficGroups_normalizedHamming_mul_left

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualSoficRootRadius
theorem _root_.solution
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G) (l : List G) :
    Tendsto
      (fun n =>
        SoficGroups.normalizedHamming
          ((A.model n).action l.prod)
          ((l.map (A.model n).action).prod))
      atTop (𝓝 0) := by
  induction l with
  | nil =>
      simp [SoficGroups.PermutationModel.map_one,
        SoficGroups.normalizedHamming_self]
  | cons g l ih =>
      simp only [List.map_cons, List.prod_cons]
      have hmul := A.multiplicative g l.prod
      have hupper :
          Tendsto
            (fun n =>
              SoficGroups.normalizedHamming
                  ((A.model n).action (g * l.prod))
                  ((A.model n).action g * (A.model n).action l.prod) +
                SoficGroups.normalizedHamming
                  ((A.model n).action l.prod)
                  ((l.map (A.model n).action).prod))
            atTop (𝓝 0) := by
        simpa using hmul.add ih
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
end SoficGroups.KunActualSoficRootRadius
