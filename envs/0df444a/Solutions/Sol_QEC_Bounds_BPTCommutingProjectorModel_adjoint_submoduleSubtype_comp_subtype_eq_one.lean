-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.adjoint_submoduleSubtype_comp_subtype_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:21:02.802239+00:00
-- url     : https://prove2.me/submissions/4183272f-9faa-46be-9e53-1ad31e2a68d1

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Embedding
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_submoduleSubtype_apply_subtype


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
    (LinearMap.adjoint p.subtype).comp p.subtype = (1 : Semantics.Operator p) := by
  apply LinearMap.ext
  intro vector
  change LinearMap.adjoint p.subtype (p.subtype vector) = vector
  exact adjoint_submoduleSubtype_apply_subtype p vector
end QEC.Bounds.BPTCommutingProjectorModel
