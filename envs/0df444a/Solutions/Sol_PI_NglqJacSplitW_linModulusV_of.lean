-- Prove2me | solution 1 for PI.NglqJacSplitW.linModulusV_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:01.072005+00:00
-- url     : https://prove2.me/submissions/794ab249-3d30-42e2-9c87-c81cae060438

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_Transport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Matrix
open scoped ENNReal NNReal Pointwise
open PI PI.NglqJacSplitW
namespace PI.NglqJacSplitW
theorem _root_.solution (h : LinModulus) : LinModulusV := by
  intro F _ _ _ _ _ _ V _ _ _ _ _ ι _ _ ⟨e⟩ f hf ν hν S hS
  haveI := hν
  letI : MeasurableSpace (ι → F) := borel (ι → F)
  haveI : BorelSpace (ι → F) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup V :=
    Topology.IsInducing.topologicalAddGroup e e.toHomeomorph.isInducing
  let E : V ≃ᵐ (ι → F) := e.toHomeomorph.toMeasurableEquiv
  have hE : ∀ x, E x = e x := fun x => rfl
  haveI : (ν.map E).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map ν e.toLinearEquiv.toAddEquiv e.continuous e.symm.continuous
  let g : (ι → F) →ₗ[F] (ι → F) :=
    (e.toLinearEquiv : V →ₗ[F] (ι → F)) ∘ₗ f ∘ₗ (e.toLinearEquiv.symm : (ι → F) →ₗ[F] V)
  have hdet : (LinearMap.toMatrix' g).det = LinearMap.det f := by
    rw [LinearMap.det_toMatrix']
    exact LinearMap.det_conj f e.toLinearEquiv
  have hmv : ∀ x, (LinearMap.toMatrix' g) *ᵥ x = g x := fun x => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have himg : (fun x => (LinearMap.toMatrix' g) *ᵥ x) '' (E '' S) = E '' (f '' S) := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext x
    rw [hmv, hE, hE]
    simp [g]
  have hES : MeasurableSet (E '' S) := E.measurableSet_image.mpr hS
  have key := h F ι (LinearMap.toMatrix' g) (by rw [hdet]; exact hf) (ν.map E) inferInstance
    (E '' S) hES
  rw [himg, hdet, MeasurableEquiv.map_apply, MeasurableEquiv.map_apply,
    E.preimage_image, E.preimage_image] at key
  exact key
end PI.NglqJacSplitW
