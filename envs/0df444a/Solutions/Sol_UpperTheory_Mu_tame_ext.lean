-- Prove2me | solution 1 for UpperTheory.Mu.tame_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:14:07.490674+00:00
-- url     : https://prove2.me/submissions/6d2a554c-08e8-4109-b529-4c9c85f16ce1

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_TorsionReduceInjective
import Theorems.Thm_UpperTheory_Mu_torsion_reduce_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Classical
noncomputable section
open UpperTheory UpperTheory.Mu
namespace UpperTheory.Mu
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)), ((NumberField.Units.torsionOrder L : ℕ) : 𝓞 L) ∉ v.asIdeal → NumberField.Units.torsionOrder L + 1 < Ideal.absNorm v.asIdeal → ∀ ε : NumberField.Units.torsion L →* ℂˣ, ∃ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ, θ ≠ 1 ∧ ∀ ζ : NumberField.Units.torsion L, θ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom (ζ : (𝓞 L)ˣ)) = ε ζ := by
  intro L _ _ v hw hN ε
  haveI := v.isMaximal
  have hf := torsion_reduce_injective L v hw
  set f := (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom).comp
    (NumberField.Units.torsion L).subtype with hf_def
  have hcardk : Nat.card (𝓞 L ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcardk]; omega)
  let e := MonoidHom.ofInjective hf
  obtain ⟨θ0, hθ0⟩ := MonoidHom.domRestrict_surjective (M := ℂ) f.range (ε.comp e.symm.toMonoidHom)
  have hext : ∀ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ,
      MonoidHom.domRestrictHom f.range ℂˣ θ = ε.comp e.symm.toMonoidHom →
      ∀ ζ : NumberField.Units.torsion L,
        θ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom (ζ : (𝓞 L)ˣ)) = ε ζ := by
    intro θ hθ ζ
    have h := DFunLike.congr_fun hθ (e ζ)
    have h2 : e.symm (e ζ) = ζ := e.symm_apply_apply ζ
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, h2] at h
    rw [← h]
    rfl
  have hS : Nat.card f.range = NumberField.Units.torsionOrder L := by
    rw [← Nat.card_congr e.toEquiv]
    rfl
  have hG : Nat.card (𝓞 L ⧸ v.asIdeal)ˣ = Ideal.absNorm v.asIdeal - 1 := by
    letI : Field (𝓞 L ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    have h := Nat.card_units (𝓞 L ⧸ v.asIdeal)
    rw [hcardk] at h
    exact h
  have hq : 2 ≤ Nat.card ((𝓞 L ⧸ v.asIdeal)ˣ ⧸ f.range) := by
    have h := f.range.card_eq_card_quotient_mul_card_subgroup
    rw [hG, hS] at h
    by_contra hlt
    push_neg at hlt
    interval_cases hc : Nat.card ((𝓞 L ⧸ v.asIdeal)ˣ ⧸ f.range) <;> omega
  have hker : 2 ≤ Nat.card (MonoidHom.domRestrictHom f.range ℂˣ).ker := by
    rw [CommGroup.card_domRestrictHom_ker]
    exact hq
  haveI : Finite (MonoidHom.domRestrictHom f.range ℂˣ).ker := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial (MonoidHom.domRestrictHom f.range ℂˣ).ker :=
    Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨χ, hχ⟩ := exists_ne (1 : (MonoidHom.domRestrictHom f.range ℂˣ).ker)
  by_cases h0 : θ0 = 1
  · refine ⟨θ0 * χ.1, ?_, ?_⟩
    · rw [h0, one_mul]
      intro h
      exact hχ (Subtype.ext h)
    · apply hext
      rw [map_mul, hθ0, MonoidHom.mem_ker.1 χ.2, mul_one]
  · exact ⟨θ0, h0, hext θ0 hθ0⟩
end UpperTheory.Mu
