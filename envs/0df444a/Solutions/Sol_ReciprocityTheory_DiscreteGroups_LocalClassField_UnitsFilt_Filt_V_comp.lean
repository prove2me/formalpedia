-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt.V_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:30.885222+00:00
-- url     : https://prove2.me/submissions/af3ff1d0-659b-4e66-a23d-83703300b9cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_V_le_zero
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_mkU_val
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_mkU_mem
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_div_mem_V

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
open Finset
variable {R : Type*} [Field R] (G : Type*) [Group G] [Fintype G] [MulSemiringAction G R]
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt
variable {G} {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)
include h
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt
theorem _root_.solution (v : ℕ → Rˣ) (hv : ∀ k, v k ∈ h.V k) :
    ∃ s ∈ h.V 0, ∀ n, s / ∏ k ∈ range n, v k ∈ h.V n := by
  have hP : ∀ n, ∏ k ∈ range n, v k ∈ h.V 0 := fun n =>
    (h.V 0).prod_mem fun k _ => h.V_le_zero k (hv k)
  have hx : ∀ k, ((v k : R) - 1) * ((∏ j ∈ range k, v j : Rˣ) : R) ∈ I k := fun k =>
    h.mul_unit (hv k) (hP k)
  obtain ⟨t, ht⟩ := h.comp _ hx
  have hsum : ∀ n, ∑ k ∈ range n, ((v k : R) - 1) * ((∏ j ∈ range k, v j : Rˣ) : R) =
      ((∏ j ∈ range n, v j : Rˣ) : R) - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih, prod_range_succ, Units.val_mul]; ring
  have ht0 : t ∈ I 0 := by simpa using ht 0
  refine ⟨h.mkU t ht0, h.mkU_mem t ht0, fun n => h.div_mem_V (hP n) ?_⟩
  have := ht n
  rw [hsum] at this
  rw [mkU_val]
  convert this using 1
  ring
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt
