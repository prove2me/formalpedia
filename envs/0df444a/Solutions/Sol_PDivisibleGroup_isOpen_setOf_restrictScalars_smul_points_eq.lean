-- Prove2me | solution 1 for PDivisibleGroup.isOpen_setOf_restrictScalars_smul_points_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ddde2b0a-39fa-5808-acb5-d91cb0a29356

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_isOpen_setOf_restrictScalars_smul_points_eq

set_option autoImplicit false

namespace HTCONT

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
variable (K L : Type) [Field K] [Field L] [Algebra R K] [Algebra R L] [Algebra K L]
variable [IsScalarTower R K L]

theorem restrictScalars_mul (σ τ : L ≃ₐ[K] L) :
    (σ * τ).restrictScalars R = σ.restrictScalars R * τ.restrictScalars R :=
  AlgEquiv.ext fun _ => rfl

variable {G K L}

theorem pointMap_eq_of_forall {v : ℕ} (f : G.Point L v) (τ : L ≃ₐ[K] L)
    {ι : Type*} (b : Module.Basis ι R (G.level v))
    (hτ : ∀ i, τ (PDivisibleGroup.Point.toAlgHom f (b i)) = PDivisibleGroup.Point.toAlgHom f (b i)) :
    G.pointMap ((τ.restrictScalars R : L ≃ₐ[R] L) : L →ₐ[R] L) v f = f := by
  refine PDivisibleGroup.Point.ext fun a => ?_
  rw [PDivisibleGroup.toAlgHom_pointMap, AlgHom.comp_apply]
  change τ (PDivisibleGroup.Point.toAlgHom f a) = PDivisibleGroup.Point.toAlgHom f a

  set φ : G.level v →ₗ[R] L := (PDivisibleGroup.Point.toAlgHom f).toLinearMap with hφ
  set ψ : G.level v →ₗ[R] L :=
    ((τ.restrictScalars R : L ≃ₐ[R] L) : L →ₐ[R] L).toLinearMap ∘ₗ φ with hψ
  have hψφ : ψ = φ := b.ext fun i => by
    simp only [hψ, hφ, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
    exact hτ i
  have := LinearMap.congr_fun hψφ a
  simp only [hψ, hφ, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply] at this
  exact this

end HTCONT

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (K L : Type) [Field K] [Field L] [Algebra R K] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] [Algebra.IsAlgebraic K L] (z : G.Points L) :
    IsOpen {σ : L ≃ₐ[K] L | σ.restrictScalars R • z = z} := by
  classical

  obtain ⟨v, f, rfl⟩ := PDivisibleGroup.Points.exists_mkAdd (G := G) (L := L) z

  let b := Module.Free.chooseBasis R (G.level v)
  let S : Set L := Set.range fun i => PDivisibleGroup.Point.toAlgHom f (b i)
  haveI : Finite S := (Set.finite_range _).to_subtype
  let E : IntermediateField K L := IntermediateField.adjoin K S
  haveI : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral

  have hfix : ∀ τ : L ≃ₐ[K] L, τ ∈ E.fixingSubgroup →
      τ.restrictScalars R • G.pointsMkAdd L v (Additive.ofMul f) =
        G.pointsMkAdd L v (Additive.ofMul f) := by
    intro τ hτ
    rw [PDivisibleGroup.Points.smul_pointsMkAdd]
    congr 2
    refine HTCONT.pointMap_eq_of_forall f τ b fun i => ?_
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ _
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

  rw [isOpen_iff_forall_mem_open]
  intro σ₀ hσ₀
  refine ⟨(fun τ => σ₀⁻¹ * τ) ⁻¹' (E.fixingSubgroup : Set (L ≃ₐ[K] L)), ?_, ?_, ?_⟩
  · intro σ hσ
    have hσ' : σ₀⁻¹ * σ ∈ E.fixingSubgroup := hσ
    have hσ₀' : σ₀.restrictScalars R • G.pointsMkAdd L v (Additive.ofMul f) =
        G.pointsMkAdd L v (Additive.ofMul f) := hσ₀
    show σ.restrictScalars R • G.pointsMkAdd L v (Additive.ofMul f) =
      G.pointsMkAdd L v (Additive.ofMul f)
    conv_lhs => rw [← mul_inv_cancel_left σ₀ σ, HTCONT.restrictScalars_mul, mul_smul,
      hfix _ hσ', hσ₀']
  · exact E.fixingSubgroup_isOpen.preimage (continuous_const_mul σ₀⁻¹)
  · show σ₀⁻¹ * σ₀ ∈ E.fixingSubgroup
    rw [inv_mul_cancel]
    exact Subgroup.one_mem _

end S_PDivisibleGroup_isOpen_setOf_restrictScalars_smul_points_eq
end P2MW
export P2MW.S_PDivisibleGroup_isOpen_setOf_restrictScalars_smul_points_eq (solution)
