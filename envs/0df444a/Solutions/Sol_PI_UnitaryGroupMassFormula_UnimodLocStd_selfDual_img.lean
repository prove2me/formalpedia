-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.selfDual_img
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:34:50.735089+00:00
-- url     : https://prove2.me/submissions/76020a1a-84af-4acf-ad51-3bddcfe990e4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_QequivApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_ExistsGoodForm
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_mem_dualLat_iff
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_mem_imgLat_iff
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply



set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (H : Sesq V) (g : V ≃ₗ[ℂ] V) (hg : IsIsom H H (g : V →ₗ[ℂ] V)) {Λ : AddSubgroup V}
    (hΛ : IsSelfDual H Λ) : IsSelfDual H (imgLat (g : V →ₗ[ℂ] V) Λ) := by
  have hg' : ∀ a b, H (g a) (g b) = H a b := fun a b => by simpa using hg a b
  unfold IsSelfDual at hΛ ⊢
  ext x
  rw [mem_dualLat_iff, mem_imgLat_iff]
  obtain ⟨x₀, rfl⟩ := g.surjective x
  have key : (∀ y ∈ imgLat (g : V →ₗ[ℂ] V) Λ, ∃ k : ℤ, altE H (g x₀) y = k) ↔ x₀ ∈ dualLat H Λ := by
    rw [mem_dualLat_iff]
    constructor
    · intro h y hy
      obtain ⟨k, hk⟩ := h (g y) ((mem_imgLat_iff g Λ _).mpr ⟨y, hy, rfl⟩)
      exact ⟨k, by rw [← hk]; simp only [altE]; rw [hg']⟩
    · intro h y' hy'
      obtain ⟨y, hy, rfl⟩ := (mem_imgLat_iff g Λ y').mp hy'
      obtain ⟨k, hk⟩ := h y hy
      exact ⟨k, by simp only [altE]; rw [hg']; exact hk⟩
  rw [key, hΛ]
  constructor
  · intro h
    exact ⟨x₀, h, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    rwa [g.injective hxy] at hy
end PI.UnitaryGroupMassFormula.UnimodLocStd
