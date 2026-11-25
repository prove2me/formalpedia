-- Prove2me | solution 1 for PI.ZW.transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:33:53.480891+00:00
-- url     : https://prove2.me/submissions/a04e903a-3580-4c82-957b-95243ad58d1c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Transfer
import Theorems.Thm_PI_ZW_differentiable_gammaFactor_inv
import Theorems.Thm_PI_ZW_gammaFactor_ne_zero_of_re_pos
import Theorems.Thm_PI_ZW_isPrimitive_inv
import Theorems.Thm_PI_ZW_rootNumber_ne_zero
import Theorems.Thm_PI_ZW_isOpen_strip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open PI PI.ZW
open DirichletCharacter
namespace PI.ZW
theorem _root_.solution : Transfer := by
  intro N _ χ hχ ρ h0 h1 hz
  have hχi := isPrimitive_inv hχ
  have hstrip : ∀ s : ℂ, 0 < s.re → s.re < 1 → 0 < (1 - s).re := fun s _ h => by simp; linarith
  have hfun : ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ⁻¹ (1 - s) =
      ((N : ℂ) ^ (s - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ s * (gammaFactor χ⁻¹ (1 - s))⁻¹) *
        DirichletCharacter.LFunction χ s := by
    intro s hs0 hs1
    have h1s := hstrip s hs0 hs1
    have hg1 := gammaFactor_ne_zero_of_re_pos χ⁻¹ h1s
    have hg0 := gammaFactor_ne_zero_of_re_pos χ hs0
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s)
        (Or.inl fun h => by rw [h] at h1s; simp at h1s),
      hχi.completedLFunction_one_sub s, inv_inv,
      DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl fun h => by rw [h] at hs0; simp at hs0)]
    field_simp
  refine ⟨by rw [hfun ρ h0 h1, hz, mul_zero], ?_⟩
  have hρU : {s : ℂ | 0 < s.re ∧ s.re < 1} ∈ 𝓝 ρ := isOpen_strip.mem_nhds ⟨h0, h1⟩
  have hHd : DifferentiableOn ℂ (fun s : ℂ => (N : ℂ) ^ (s - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ s *
      (gammaFactor χ⁻¹ (1 - s))⁻¹) {s | 0 < s.re ∧ s.re < 1} := by
    intro s hs
    have hg0 := gammaFactor_ne_zero_of_re_pos χ hs.1
    have hdg : DifferentiableAt ℂ (gammaFactor χ) s := by
      have h := ((differentiable_gammaFactor_inv χ) s).inv (inv_ne_zero hg0)
      have e : (fun x => (gammaFactor χ x)⁻¹)⁻¹ = gammaFactor χ := funext fun x => by
        simp only [Pi.inv_apply, inv_inv]
      rwa [e] at h
    have hdg1 : DifferentiableAt ℂ (fun s => (gammaFactor χ⁻¹ (1 - s))⁻¹) s :=
      ((differentiable_gammaFactor_inv χ⁻¹) (1 - s)).comp s ((differentiableAt_const 1).sub differentiableAt_id)
    have hcp : DifferentiableAt ℂ (fun s : ℂ => (N : ℂ) ^ (s - 1 / 2)) s :=
      (differentiableAt_id.sub_const _).const_cpow (Or.inl (by exact_mod_cast NeZero.ne N))
    exact (((hcp.mul_const _).mul hdg).mul hdg1).differentiableWithinAt
  have hLd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {s | 0 < s.re ∧ s.re < 1} :=
    fun s hs => (DirichletCharacter.differentiableAt_LFunction χ s
      (Or.inl fun h => by rw [h] at hs; simp at hs)).differentiableWithinAt
  have hHa := hHd.analyticAt hρU
  have hLa := hLd.analyticAt hρU
  have hH0 : (N : ℂ) ^ (ρ - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ ρ * (gammaFactor χ⁻¹ (1 - ρ))⁻¹ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (rootNumber_ne_zero hχi))
      (gammaFactor_ne_zero_of_re_pos χ h0)) (inv_ne_zero (gammaFactor_ne_zero_of_re_pos χ⁻¹ (hstrip ρ h0 h1)))
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp [NeZero.ne N]
  have key : analyticOrderAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) =
      analyticOrderAt (DirichletCharacter.LFunction χ) ρ := by
    have e1 := analyticOrderAt_comp_of_deriv_ne_zero (f := DirichletCharacter.LFunction χ⁻¹)
      (g := fun s : ℂ => 1 - s) (z₀ := ρ) (analyticAt_const.sub analyticAt_id) (by simp)
    rw [← e1]
    have e2 : (DirichletCharacter.LFunction χ⁻¹ ∘ fun s : ℂ => 1 - s) =ᶠ[𝓝 ρ]
        ((fun s : ℂ => (N : ℂ) ^ (s - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ s * (gammaFactor χ⁻¹ (1 - s))⁻¹) *
          DirichletCharacter.LFunction χ) :=
      Filter.eventually_of_mem hρU fun s hs => hfun s hs.1 hs.2
    rw [analyticOrderAt_congr e2, analyticOrderAt_mul hHa hLa, (hHa.analyticOrderAt_eq_zero).mpr hH0, zero_add]
  have e : analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ =
      analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) := by
    simp only [analyticOrderNatAt, key]
  exact e.le
end PI.ZW
