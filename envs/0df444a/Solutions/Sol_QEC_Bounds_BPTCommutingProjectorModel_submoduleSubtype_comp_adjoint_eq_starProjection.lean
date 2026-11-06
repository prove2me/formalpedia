-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.submoduleSubtype_comp_adjoint_eq_starProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:21:12.372672+00:00
-- url     : https://prove2.me/submissions/8cdf78aa-1736-47a9-b782-b754d16a17b6

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Embedding

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (p : Submodule Complex H) :
    p.subtype.comp (LinearMap.adjoint p.subtype) = p.starProjection.toLinearMap := by
  apply LinearMap.ext
  intro vector
  change p.subtype (LinearMap.adjoint p.subtype vector) = p.starProjection vector
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact p.coe_mem _
  · intro test htest
    let testInSubmodule : p := ⟨test, htest⟩
    have hinner :
        inner Complex (p.subtype (LinearMap.adjoint p.subtype vector)) test =
          inner Complex vector test := by
      calc
        inner Complex (p.subtype (LinearMap.adjoint p.subtype vector)) test =
            inner Complex (LinearMap.adjoint p.subtype vector) testInSubmodule := rfl
        _ = inner Complex vector (p.subtype testInSubmodule) :=
          LinearMap.adjoint_inner_left p.subtype testInSubmodule vector
        _ = inner Complex vector test := rfl
    rw [inner_sub_left, hinner, sub_self]
end QEC.Bounds.BPTCommutingProjectorModel
