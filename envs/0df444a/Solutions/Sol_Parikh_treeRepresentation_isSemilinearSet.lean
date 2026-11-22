-- Prove2me | solution 1 for Parikh.treeRepresentation_isSemilinearSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:52:00.012913+00:00
-- url     : https://prove2.me/submissions/eb85bc2c-54a6-4a6a-82b1-354f2c8b0bf3

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Definitions.Def_LeanPool_Parikh_FiniteRepresentation
public import Theorems.Thm_Parikh_bases_finite
public import Theorems.Thm_Parikh_bounded_cycles_finite
public import Theorems.Thm_Parikh_component_isLinearSet


set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [Finite T] [DecidableEq T]
    (g : ContextFreeGrammar T) : IsSemilinearSet (treeRepresentation g) := by
  classical
  let bases := (bases_finite g).toFinset
  let cycles := (bounded_cycles_finite g).toFinset
  have hunion : treeRepresentation g =
      ⋃ B ∈ bases, ⋃ D ∈ cycles.powerset.filter (ContextsActivatable g B),
        (contextComponent B D).denotation := by
    ext v
    simp only [treeRepresentation, Set.mem_ofPred_eq, Set.mem_iUnion,
      Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨B, D, hB, hD, hactive, hv⟩
      refine ⟨B, (bases_finite g).mem_toFinset.mpr hB, D, ⟨?_, hactive⟩, hv⟩
      intro C hC
      exact (bounded_cycles_finite g).mem_toFinset.mpr (hD C hC)
    · rintro ⟨B, hB, D, ⟨hD, hactive⟩, hv⟩
      exact ⟨B, D, (bases_finite g).mem_toFinset.mp hB,
        fun C hC => (bounded_cycles_finite g).mem_toFinset.mp (hD hC), hactive, hv⟩
  rw [hunion]
  exact IsSemilinearSet.biUnion_finset fun B _ =>
    IsSemilinearSet.biUnion_finset fun D _ =>
      (component_isLinearSet (contextComponent B D)).isSemilinearSet
end Parikh
