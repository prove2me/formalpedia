-- Prove2me | solution 1 for SensitivityPoA.NoUniform.poa_costNormalize
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:39:20.760998+00:00
-- url     : https://prove2.me/submissions/d4ce69ca-4a82-4716-a500-f2483c964b28

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_NoUniform_Setting

set_option autoImplicit false
open SensitivityPoA.NoUniform KellyStochasticNetworks
open scoped Pointwise

theorem solution (N : Network) (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (υ : ℝ) (hυ : 0 < υ) :
    costNormalize υ Γ ∈ gameSpace N ∧ PoA (costNormalize υ Γ) = PoA Γ := by
  have hυ0 : 0 ≤ υ⁻¹ := inv_nonneg.mpr hυ.le
  obtain ⟨⟨hcf, hd⟩, hpos, hτ⟩ := hΓ
  refine ⟨⟨⟨fun j => ?_, hd⟩, hpos, fun j x hx hxT => ?_⟩, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hcf j
    refine ⟨?_, ?_, fun x hx => ?_⟩
    · exact h1.div_const υ
    · intro x hx y hy hxy
      exact div_le_div_of_nonneg_right (h2 hx hy hxy) hυ.le
    · exact div_nonneg (h3 x hx) hυ.le
  · exact div_pos (hτ j x hx hxT) hυ
  · have hflow : ∀ f, IsFlow (costNormalize υ Γ) f ↔ IsFlow Γ f := fun f => Iff.rfl
    have hcost : ∀ f, cost (costNormalize υ Γ) f = υ⁻¹ * cost Γ f := by
      intro f
      unfold cost costNormalize
      simp only
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    have hWE : ∀ f, IsWE (costNormalize υ Γ) f ↔ IsWE Γ f := by
      intro f
      unfold IsWE IsWardropEquilibrium
      simp only [costNormalize]
      refine and_congr Iff.rfl (forall_congr' fun r => forall_congr' fun r' =>
        imp_congr_right fun _ => imp_congr_right fun _ => ?_)
      simp only [div_mul_eq_mul_div, ← Finset.sum_div]
      exact div_le_div_iff_of_pos_right hυ
    have hWEc : WECost (costNormalize υ Γ) = υ⁻¹ * WECost Γ := by
      unfold WECost
      have : cost (costNormalize υ Γ) '' {f | IsWE (costNormalize υ Γ) f}
          = υ⁻¹ • (cost Γ '' {f | IsWE Γ f}) := by
        rw [← Set.image_smul, Set.image_image]
        ext x
        simp only [Set.mem_image, Set.mem_setOf_eq, hcost, hWE, smul_eq_mul]
      rw [this, Real.sSup_smul_of_nonneg hυ0, smul_eq_mul]
    have hSOc : SOCost (costNormalize υ Γ) = υ⁻¹ * SOCost Γ := by
      unfold SOCost
      have : cost (costNormalize υ Γ) '' {f | IsFlow (costNormalize υ Γ) f}
          = υ⁻¹ • (cost Γ '' {f | IsFlow Γ f}) := by
        rw [← Set.image_smul, Set.image_image]
        ext x
        simp only [Set.mem_image, Set.mem_setOf_eq, hcost, hflow, smul_eq_mul]
      rw [this, Real.sInf_smul_of_nonneg hυ0, smul_eq_mul]
    unfold PoA
    rw [hWEc, hSOc, mul_div_mul_left _ _ (inv_ne_zero hυ.ne')]
