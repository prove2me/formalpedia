-- Prove2me | solution 1 for QEC.Semantics.KnillLaflamme.unitaryTransport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:10:59.400818+00:00
-- url     : https://prove2.me/submissions/cf7c9bdf-ae3a-42e3-a983-7ec99540edc3

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
noncomputable section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
open QEC.Semantics.KnillLaflamme
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
namespace QEC.Semantics.KnillLaflamme
theorem _root_.solution
    (U : UnitaryTransport H K) {C : QuantumCode H} {D : QuantumCode K}
    {errors : Set (Operator H)}
    (hCD : QuantumCode.TransportedBy U C D)
    (hKL : KnillLaflammeCriterion H C errors) :
    KnillLaflammeCriterion K D (Set.image (UnitaryTransport.conjOperator U) errors) := by
  rcases hKL with ⟨scalar, hscalar⟩
  let scalarTransported : Operator K → Operator K → Complex :=
    fun E F =>
      scalar
        (U.toLinearEquiv.symm.toLinearMap.comp (E.comp U.toLinearEquiv.toLinearMap))
        (U.toLinearEquiv.symm.toLinearMap.comp (F.comp U.toLinearEquiv.toLinearMap))
  refine ⟨scalarTransported, ?_⟩
  intro E hE F hF x hx y hy
  rcases hE with ⟨E₀, hE₀, rfl⟩
  rcases hF with ⟨F₀, hF₀, rfl⟩
  let x₀ : H := U.toLinearEquiv.symm x
  let y₀ : H := U.toLinearEquiv.symm y
  have hx₀ : x₀ ∈ C.carrier := by
    have hxD : U.toLinearEquiv x₀ ∈ D.carrier := by
      simpa [x₀] using hx
    exact (hCD x₀).2 hxD
  have hy₀ : y₀ ∈ C.carrier := by
    have hyD : U.toLinearEquiv y₀ ∈ D.carrier := by
      simpa [y₀] using hy
    exact (hCD y₀).2 hyD
  have hScalarE :
      U.toLinearEquiv.symm.toLinearMap.comp
          ((U.conjOperator E₀).comp U.toLinearEquiv.toLinearMap) = E₀ := by
    ext z
    simp [UnitaryTransport.conjOperator]
  have hScalarF :
      U.toLinearEquiv.symm.toLinearMap.comp
          ((U.conjOperator F₀).comp U.toLinearEquiv.toLinearMap) = F₀ := by
    ext z
    simp [UnitaryTransport.conjOperator]
  have hxy : inner Complex x₀ y₀ = inner Complex x y := by
    simpa [x₀, y₀] using (U.map_inner x₀ y₀).symm
  calc
    inner Complex (U.conjOperator E₀ x) (U.conjOperator F₀ y)
        = inner Complex (U.toLinearEquiv (E₀ x₀)) (U.toLinearEquiv (F₀ y₀)) := by
          simp [UnitaryTransport.conjOperator, x₀, y₀]
    _ = inner Complex (E₀ x₀) (F₀ y₀) := U.map_inner (E₀ x₀) (F₀ y₀)
    _ = scalar E₀ F₀ * inner Complex x₀ y₀ := hscalar hE₀ hF₀ x₀ hx₀ y₀ hy₀
    _ = scalarTransported (U.conjOperator E₀) (U.conjOperator F₀) *
          inner Complex x y := by
        simp [scalarTransported, hScalarE, hScalarF, hxy]
end QEC.Semantics.KnillLaflamme
