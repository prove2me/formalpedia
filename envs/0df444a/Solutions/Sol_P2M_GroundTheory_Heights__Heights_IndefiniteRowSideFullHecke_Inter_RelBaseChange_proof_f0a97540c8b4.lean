-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_RelBaseChange_proof_f0a97540c8b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:58:55.943045+00:00
-- url     : https://prove2.me/submissions/9a774f9e-b4c5-438d-8e41-704a83771a73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RelBaseChangeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRelBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_RelBaseChange_aeval_map_7e88154197c4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial TensorProduct
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace RelBaseChange
theorem _root_.solution : RelBaseChange.Statement := by
  intro F F' _ _ _ σ τ g
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [RingHom.mem_ker] at hp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    erw [RelBaseChange.aeval_map g p, hp, map_zero]
  · intro x hx
    rw [RingHom.mem_ker] at hx
    let Φ : MvPolynomial σ F →ₗ[F] MvPolynomial τ F := (aeval g).toLinearMap
    let eσ := MvPolynomial.algebraTensorAlgEquiv (σ := σ) F F'
    let eτ := MvPolynomial.algebraTensorAlgEquiv (σ := τ) F F'
    have key : ∀ y : F' ⊗[F] MvPolynomial σ F,
        eτ (AlgebraTensorModule.lTensor F' F' Φ y) =
          aeval (fun s => MvPolynomial.map (algebraMap F F') (g s)) (eσ y) := by
      intro y
      induction y with
      | zero => simp
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul a p =>
        simp only [AlgebraTensorModule.lTensor_tmul, eσ, eτ, algebraTensorAlgEquiv_tmul, map_smul,
          RelBaseChange.aeval_map, Φ, AlgHom.toLinearMap_apply]
    have hy : eσ.symm x ∈ LinearMap.ker (AlgebraTensorModule.lTensor F' F' Φ) := by
      rw [LinearMap.mem_ker]
      apply eτ.injective
      rw [key, AlgEquiv.apply_symm_apply, hx, map_zero]
    rw [Module.Flat.ker_lTensor_eq] at hy
    obtain ⟨z, hz⟩ := hy
    have hx' : x = eσ (AlgebraTensorModule.lTensor F' F' (LinearMap.ker Φ).subtype z) := by
      rw [hz, AlgEquiv.apply_symm_apply]
    rw [hx']
    clear hz hx'
    induction z with
    | zero => simp
    | add y z hy hz => rw [map_add, map_add]; exact Ideal.add_mem _ hy hz
    | tmul a k =>
      simp only [AlgebraTensorModule.lTensor_tmul, Submodule.coe_subtype, eσ,
        algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul]
      refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
      rw [RingHom.mem_ker]
      exact k.2
end RelBaseChange
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
