-- Prove2me | solution 1 for SimpleGraph.RamseyBound.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:33.857811+00:00
-- url     : https://prove2.me/submissions/b46dcfff-3092-4d50-ae96-dad42e7a89ed

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
public import Theorems.Thm_SimpleGraph_Bireservoir_card_redPivot_pool_add_card_bluePivot_pool
public import Theorems.Thm_SimpleGraph_Bireservoir_exists_of_ramseyBound
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
namespace RamseyBound
theorem _root_.solution {a b r s : ℕ} (ha : RamseyBound a r (s + 1))
    (hb : RamseyBound b (r + 1) s) (hab : 0 < a + b) : RamseyBound (a + b) (r + 1) (s + 1) := by
  classical
  intro G
  set S := Bireservoir.ofPool (G := G) univ with hS
  have hv : (⟨0, hab⟩ : Fin (a + b)) ∈ S.pool := mem_univ _
  have hpart := S.card_redPivot_pool_add_card_bluePivot_pool hv
  have hcard : #S.pool = a + b := by simp [hS]
  by_cases hred : a ≤ #(S.redPivot hv).pool
  · exact (S.redPivot hv).exists_of_ramseyBound (by simpa [hS] using ha) hred
  · exact (S.bluePivot hv).exists_of_ramseyBound (by simpa [hS] using hb) (by omega)
end RamseyBound
end SimpleGraph
