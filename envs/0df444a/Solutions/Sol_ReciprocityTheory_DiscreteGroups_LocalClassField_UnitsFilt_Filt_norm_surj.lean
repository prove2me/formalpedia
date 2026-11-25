-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt.norm_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:21.226795+00:00
-- url     : https://prove2.me/submissions/e934cd7a-5370-46e7-a496-61b12e491a17

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_act_val
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_normU_val
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_smul_prod_univ
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_normU_mem
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_V_comp
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_V_sep
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_div_mem_V
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_mkU_mem
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_mkU_val
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_prod_one_add
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_exists_of_approx


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
variable {R : Type*} [Field R] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G R]
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt
variable {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)
include h
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt
theorem _root_.solution (u : Rˣ) (hu : (u : R) - 1 ∈ I 0) (hfix : ∀ g : G, g • (u : R) = u) :
    ∃ v : Rˣ, (v : R) - 1 ∈ I 0 ∧ ∏ g : G, g • (v : R) = u := by
  let Z : Subgroup Rˣ :=
    { carrier := {u | ∀ g : G, act g u = u}
      one_mem' := fun g => map_one _
      mul_mem' := fun {a b} ha hb g => by rw [map_mul, ha g, hb g]
      inv_mem' := fun {a} ha g => by rw [map_inv, ha g] }
  have step : ∀ n, ∀ u ∈ h.V n, u ∈ Z → ∃ v ∈ h.V n, u / normU G v ∈ h.V (n + 1) := by
    intro n u hu hZ
    have hx : ∀ g : G, g • ((u : R) - 1) = (u : R) - 1 := fun g => by
      rw [smul_sub, smul_one, ← act_val, hZ g]
    have hy : e ((u : R) - 1) ∈ I n := h.e_mem n _ hu
    have htr : ∑ g : G, g • e ((u : R) - 1) = (u : R) - 1 := by
      conv_rhs => rw [← h.e_sum ((u : R) - 1)]
      exact Finset.sum_congr rfl fun g _ => by rw [hx]
    refine ⟨h.mkU _ (h.le_zero n hy), h.mkU_mem _ hy, h.div_mem_V (h.normU_mem (h.mkU_mem _ (h.le_zero n hy))) ?_⟩
    have hp := h.prod_one_add (n := n) univ (fun g : G => g • e ((u : R) - 1)) (fun g _ => h.smul n g _ hy)
    rw [htr] at hp
    rw [normU_val, mkU_val]
    simp only [smul_add, smul_one]
    have := (I (n + 1)).neg_mem hp
    convert this using 1
    ring
  obtain ⟨v, hv, hvu⟩ := exists_of_approx h.V h.V_comp h.V_sep Z (normU G)
    (fun n u hu => h.normU_mem hu)
    (fun u g => Units.ext (by rw [act_val, normU_val, smul_prod_univ])) step u hu
    (fun g => Units.ext (hfix g))
  exact ⟨v, hv, by rw [← normU_val, hvu]⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt
