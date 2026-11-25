-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_model_of_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:23.685364+00:00
-- url     : https://prove2.me/submissions/74f939f9-bb6a-4b0a-b68e-96191be1d00f

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_hausdorff_local_field
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_integers_iff_norm_of_homeomorph

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ValuativeRel Function Filter Topology
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [ContinuousSMul ℚ_[p] K] :
    ∃ m : Model K p, ∀ x : ℚ_[p], (m.e (algebraMap ℚ_[p] K x) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) x := by
  have := hausdorff_local_field K
  let φ : K →ₐ[ℚ_[p]] PadicAlgCl p := IsAlgClosed.lift
  let e : K ≃ₐ[ℚ_[p]] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  have hfin : FiniteDimensional ℚ_[p] φ.fieldRange := Module.Finite.equiv e.toLinearEquiv
  let _ : Algebra K (PadicAlgCl p) := φ.toRingHom.toAlgebra
  have : IsScalarTower ℚ_[p] K (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have : Algebra.IsAlgebraic K (PadicAlgCl p) := Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) K
  have : IsAlgClosure K (PadicAlgCl p) := ⟨inferInstance, inferInstance⟩
  let E : AlgebraicClosure K ≃ₐ[K] PadicAlgCl p := IsAlgClosure.equiv K _ _
  have hhomeo : IsHomeomorph e.toRingEquiv :=
    (e.toLinearEquiv.toContinuousLinearEquiv.toHomeomorph).isHomeomorph
  refine ⟨{ K' := φ.fieldRange, fin := hfin, e := e.toRingEquiv, E := E.toRingEquiv, comm := ?_, homeo := hhomeo, int := ?_ }, ?_⟩
  · intro x
    exact E.commutes x
  · intro x
    exact mem_integers_iff_norm_of_homeomorph e.toRingEquiv hhomeo x
  · intro x
    exact φ.commutes x
end ReciprocityTheory.DiscreteGroups.LocalClassField
