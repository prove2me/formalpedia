-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.UG.exists_isom_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:07:17.299965+00:00
-- url     : https://prove2.me/submissions/64469be2-3544-4c7a-96ad-a00f0343d61d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomMove
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_star_h
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_exists_quasi
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.UG
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}
namespace PI.UnitaryGroupMassFormula.CntFormula.UG
theorem _root_.solution (hS : IsHermSemilocal S) (hs : h.IsSymm) {x z : V} {u : K} (hu0 : u ≠ 0)
    (hus : star u = u) (hx : h x x = u) (hz : h z z = u) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = z ∧ ∀ v, h x v = 0 → h z v = 0 → τ v = v := by
  have hsy : ∀ a b : V, star (h a b) = h b a := star_h hs
  have key : ∀ y : V, h y y = u → h z y ≠ u →
      ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ y = z ∧ ∀ v, h y v = 0 → h z v = 0 → τ v = v := by
    intro y hy hne
    have hp : u - h z y ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hsp : star (u - h z y) ≠ 0 := star_ne_zero.mpr hp
    have hww : h (y - z) (y - z) = (u - h z y) + star (u - h z y) := by
      simp only [map_sub, LinearMap.sub_apply]
      rw [hy, hz, star_sub, hus, hsy]
      ring
    obtain ⟨τ, hτ, hf⟩ := exists_quasi hs (y - z) (a := (u - h z y)⁻¹) (by
      rw [hww, star_inv₀]
      field_simp
      ring)
    refine ⟨τ, hτ, ?_, ?_⟩
    · have hyz : h (y - z) y = u - h z y := by
        simp only [map_sub, LinearMap.sub_apply, hy]
      rw [hf, hyz, inv_mul_cancel₀ hp, one_smul]
      abel
    · intro v hyv hzv
      rw [hf]
      simp only [map_sub, LinearMap.sub_apply, hyv, hzv, sub_zero, mul_zero, zero_smul]
  by_cases hne : h z x = u
  · obtain ⟨θ, -, hθ⟩ := hS.unram
    have hd : θ - star θ ≠ 0 := hθ.1
    have hθ0 : θ ≠ 0 := by
      rintro rfl
      simp at hd
    have hsθ : star θ ≠ 0 := star_ne_zero.mpr hθ0
    have hcc : θ * (star θ)⁻¹ * (star θ * θ⁻¹) = 1 := by field_simp
    have hc1 : θ * (star θ)⁻¹ ≠ 1 := by
      intro h1
      apply hd
      field_simp at h1
      exact sub_eq_zero.mpr h1
    obtain ⟨τ₁, hτ₁, hf₁⟩ := exists_quasi hs x (a := (1 - θ * (star θ)⁻¹) * u⁻¹) (by
      rw [hx]
      simp only [star_mul', star_sub, star_one, star_inv₀, star_star, hus]
      field_simp
      ring)
    have h1x : τ₁ x = (θ * (star θ)⁻¹) • x := by
      rw [hf₁, hx, mul_assoc, inv_mul_cancel₀ hu0, mul_one, sub_smul, one_smul]
      abel
    have hyy : h (τ₁ x) (τ₁ x) = u := by
      have hcx : ∀ c : K, h (c • x) (c • x) = star c * c * u := by
        intro c
        simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply, hx]
        ring
      rw [h1x, hcx, star_mul', star_inv₀, star_star]
      have e1 : star θ * (star θ)⁻¹ = 1 := mul_inv_cancel₀ hsθ
      have e2 : θ * θ⁻¹ = 1 := mul_inv_cancel₀ hθ0
      linear_combination (θ * θ⁻¹ * u) * e1 + u * e2
    have hzy : h z (τ₁ x) ≠ u := by
      rw [h1x, map_smul, smul_eq_mul, hne]
      intro h2
      apply hc1
      have := mul_right_cancel₀ hu0 (h2.trans (one_mul u).symm)
      exact this
    obtain ⟨τ₂, hτ₂, h2y, h2v⟩ := key _ hyy hzy
    refine ⟨τ₂ * τ₁, (Formalism.HermitianLatticesTheory.isom h).mul_mem hτ₂ hτ₁, ?_, ?_⟩
    · exact h2y
    · intro v hxv hzv
      have h1v : τ₁ v = v := by
        rw [hf₁, hxv, mul_zero, zero_smul, sub_zero]
      change τ₂ (τ₁ v) = v
      rw [h1v]
      refine h2v v ?_ hzv
      rw [h1x, map_smulₛₗ, LinearMap.smul_apply, hxv, smul_zero]
  · exact key x hx hne
end PI.UnitaryGroupMassFormula.CntFormula.UG
