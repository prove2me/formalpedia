-- Prove2me | solution 1 for SimpleGraph.ramseyBound_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:35:20.152802+00:00
-- url     : https://prove2.me/submissions/adef3927-eda8-44df-a992-8d4ce665f441

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Theorems.Thm_SimpleGraph_Bireservoir_ofPool_red
public import Theorems.Thm_SimpleGraph_Bireservoir_ofPool_blue
public import Theorems.Thm_SimpleGraph_Bireservoir_ofPool_pool
public import Theorems.Thm_SimpleGraph_Bireservoir_toRed_spine
public import Theorems.Thm_SimpleGraph_Bireservoir_toRed_pool
public import Theorems.Thm_SimpleGraph_Bireservoir_toBlue_spine
public import Theorems.Thm_SimpleGraph_Bireservoir_toBlue_pool
public import Theorems.Thm_SimpleGraph_Bireservoir_redPivot_red
public import Theorems.Thm_SimpleGraph_Bireservoir_redPivot_blue
public import Theorems.Thm_SimpleGraph_Bireservoir_redPivot_pool
public import Theorems.Thm_SimpleGraph_Bireservoir_bluePivot_red
public import Theorems.Thm_SimpleGraph_Bireservoir_bluePivot_blue
public import Theorems.Thm_SimpleGraph_Bireservoir_bluePivot_pool
public import Theorems.Thm_SimpleGraph_ramseyBound_of_pascal
public import Theorems.Thm_SimpleGraph_isPascal_choose
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_pool
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_spine
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_pool
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_spine
attribute [local simp] SimpleGraph.Reservoir.ofPool_pool
attribute [local simp] SimpleGraph.Reservoir.ofPool_spine
attribute [local simp] SimpleGraph.Reservoir.pivot_pool
attribute [local simp] SimpleGraph.Reservoir.pivot_spine


attribute [local simp] SimpleGraph.Bireservoir.ofPool_red
attribute [local simp] SimpleGraph.Bireservoir.ofPool_blue
attribute [local simp] SimpleGraph.Bireservoir.ofPool_pool
attribute [local simp] SimpleGraph.Bireservoir.toRed_spine
attribute [local simp] SimpleGraph.Bireservoir.toRed_pool
attribute [local simp] SimpleGraph.Bireservoir.toBlue_spine
attribute [local simp] SimpleGraph.Bireservoir.toBlue_pool
attribute [local simp] SimpleGraph.Bireservoir.redPivot_red
attribute [local simp] SimpleGraph.Bireservoir.redPivot_blue
attribute [local simp] SimpleGraph.Bireservoir.redPivot_pool
attribute [local simp] SimpleGraph.Bireservoir.bluePivot_red
attribute [local simp] SimpleGraph.Bireservoir.bluePivot_blue
attribute [local simp] SimpleGraph.Bireservoir.bluePivot_pool

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
namespace SimpleGraph
theorem _root_.solution (r s : ℕ) : RamseyBound ((r + s).choose r) (r + 1) (s + 1) := by
  simpa [show r + 1 + (s + 1) - 2 = r + s by omega] using
    ramseyBound_of_pascal isPascal_choose (r + 1) (s + 1)
end SimpleGraph
