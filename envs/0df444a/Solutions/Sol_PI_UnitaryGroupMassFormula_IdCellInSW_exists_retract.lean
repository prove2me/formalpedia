-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.IdCellInSW.exists_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:36.249547+00:00
-- url     : https://prove2.me/submissions/c2947a2e-30d0-488b-ad9e-51be6739fa2f

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Lemmata_GeneralBFactThirdTail_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdentityCellTrace_ExistsSmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IdCellInSW
variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
variable [StarRing E]
omit [StarRing E]
namespace PI.UnitaryGroupMassFormula.IdCellInSW
theorem _root_.solution (Λ : Submodule (𝓞 E) V) (hΛ : Λ.FG) (X : Submodule E V) :
    ∃ ρ : Λ →ₗ[𝓞 E] Λ, (∀ y, ((ρ y : Λ) : V) ∈ X) ∧ ∀ y : Λ, (y : V) ∈ X → ρ y = y := by
  classical
  let N : Submodule (𝓞 E) Λ := (X.restrictScalars (𝓞 E)).comap Λ.subtype
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ
  have htf : Module.IsTorsionFree (𝓞 E) (Λ ⧸ N) := by
    refine ⟨fun r hr q₁ q₂ hq => ?_⟩
    have hr0 : r ≠ 0 := hr.ne_zero
    obtain ⟨y₁, rfl⟩ := N.mkQ_surjective q₁
    obtain ⟨y₂, rfl⟩ := N.mkQ_surjective q₂
    have hq' : N.mkQ (r • (y₁ - y₂)) = 0 := by
      rw [map_smul, map_sub, smul_sub, sub_eq_zero]
      exact hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq'
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    have hmem : ((r • (y₁ - y₂) : Λ) : V) ∈ X := hq'
    have hrE : algebraMap (𝓞 E) E r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hr0
    have e : ((y₁ - y₂ : Λ) : V) = (algebraMap (𝓞 E) E r)⁻¹ • ((r • (y₁ - y₂) : Λ) : V) := by
      rw [Submodule.coe_smul, ← algebraMap_smul E r, smul_smul, inv_mul_cancel₀ hrE, one_smul]
    show ((y₁ - y₂ : Λ) : V) ∈ X
    rw [e]
    exact X.smul_mem _ hmem
  have : Module.FinitePresentation (𝓞 E) (Λ ⧸ N) := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) (Λ ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  let ρ : Λ →ₗ[𝓞 E] Λ := LinearMap.id - s ∘ₗ N.mkQ
  refine ⟨ρ, fun y => ?_, fun y hy => ?_⟩
  · have h0 : N.mkQ (ρ y) = 0 := by
      have := congrArg (fun φ => φ (N.mkQ y)) hs
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
      simp only [ρ, LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.coe_comp,
        Function.comp_apply, map_sub, this, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  · have h0 : N.mkQ y = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hy
    simp [ρ, h0]
end PI.UnitaryGroupMassFormula.IdCellInSW
