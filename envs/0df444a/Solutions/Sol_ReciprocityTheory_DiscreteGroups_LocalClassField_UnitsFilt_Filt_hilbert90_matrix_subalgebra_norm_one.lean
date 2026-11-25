-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt.hilbert90_matrix_subalgebra_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:19.307802+00:00
-- url     : https://prove2.me/submissions/feab32eb-73f8-47b5-b8f4-28f77f44235c

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_act_val
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_normU_val
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_prod_smul_smul
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_sum_pow_eq
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_telescope
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_act_mem
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_V_comp
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_V_le_zero
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
theorem _root_.solution (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (u : Rˣ) (hu : (u : R) - 1 ∈ I 0)
    (hN : ∏ g : G, g • (u : R) = 1) :
    ∃ v : Rˣ, (v : R) - 1 ∈ I 0 ∧ g₀ • (v : R) = u * v := by
  have step : ∀ n, ∀ u ∈ h.V n, u ∈ (normU G).ker →
      ∃ v ∈ h.V n, u / (act g₀ / MonoidHom.id _ : Rˣ →* Rˣ) v ∈ h.V (n + 1) := by
    intro n u hu hZ
    set x : R := (u : R) - 1 with hxdef
    have hx : x ∈ I n := hu
    have hux : (u : R) = 1 + x := by rw [hxdef]; ring
    have htr : ∑ g : G, g • x ∈ I (n + 1) := by
      have hp := h.prod_one_add (n := n) univ (fun g : G => g • x) (fun g _ => h.smul n g _ hx)
      have h1 : ∏ g : G, (1 + g • x) = 1 := by
        have := congrArg Units.val (MonoidHom.mem_ker.1 hZ)
        rw [normU_val, hux] at this
        simpa only [smul_add, smul_one, Units.val_one] using this
      rw [h1, sub_self, zero_sub] at hp
      simpa using (I (n + 1)).neg_mem hp
    set y : R := ∑ k ∈ range (orderOf g₀), ∑ j ∈ range k, g₀ ^ j • e ((g₀ ^ k)⁻¹ • x) with hydef
    have hy : y ∈ I n := (I n).sum_mem fun k _ => (I n).sum_mem fun j _ =>
      h.smul n _ _ (h.e_mem n _ (h.smul n _ _ hx))
    have hd : g₀ • y - y = x - e (∑ g : G, g • x) := by
      rw [hydef, smul_sum, ← sum_sub_distrib]
      simp only [telescope]
      rw [sum_sub_distrib, sum_pow_eq hg (fun g => g • e (g⁻¹ • x)), h.e_sum, ← map_sum,
        sum_pow_eq hg (fun g => g⁻¹ • x)]
      congr 2
      exact Fintype.sum_equiv (Equiv.inv G) _ _ fun _ => rfl
    have hy0 := h.le_zero n hy
    have hvV : h.mkU y hy0 ∈ h.V n := h.mkU_mem y hy
    refine ⟨h.mkU y hy0, hvV, h.div_mem_V
      ((h.V 0).div_mem (h.act_mem g₀ (h.V_le_zero n hvV)) (h.V_le_zero n hvV)) ?_⟩
    set z : R := (1 + y)⁻¹ - 1 with hzdef
    have hz : z ∈ I n := h.inv n y hy
    have hyz : (1 + y) * (1 + z) = 1 := by
      rw [hzdef, add_sub_cancel, mul_inv_cancel₀ (h.one_add_ne_zero hy0)]
    have hval : (((act g₀ / MonoidHom.id _ : Rˣ →* Rˣ) (h.mkU y hy0) : Rˣ) : R) = (1 + g₀ • y) * (1 + z) := by
      rw [MonoidHom.div_apply, MonoidHom.id_apply, div_eq_mul_inv, Units.val_mul, act_val,
        Units.val_inv_eq_inv_val, mkU_val, smul_add, smul_one, hzdef, add_sub_cancel]
    rw [hval, hux]
    have : 1 + x - (1 + g₀ • y) * (1 + z) = e (∑ g : G, g • x) - (g₀ • y - y) * z := by
      linear_combination -hyz - hd
    rw [this]
    exact (I (n + 1)).sub_mem (h.e_mem _ _ htr)
      (h.mul n _ _ ((I n).sub_mem (h.smul n _ _ hy) hy) (h.le_zero n hz))
  obtain ⟨v, hv, hvu⟩ := exists_of_approx h.V h.V_comp h.V_sep (normU G).ker (act g₀ / MonoidHom.id _)
    (fun n u hu => (h.V n).div_mem (h.act_mem g₀ hu) hu)
    (fun u => by
      rw [MonoidHom.mem_ker, MonoidHom.div_apply, MonoidHom.id_apply, map_div, div_eq_one]
      exact Units.ext (by rw [normU_val, normU_val, act_val, prod_smul_smul])) step u hu
    (Units.ext (by rw [normU_val, hN]; rfl))
  refine ⟨v, hv, ?_⟩
  rw [MonoidHom.div_apply, MonoidHom.id_apply, div_eq_iff_eq_mul] at hvu
  rw [← act_val, hvu, Units.val_mul]
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt
