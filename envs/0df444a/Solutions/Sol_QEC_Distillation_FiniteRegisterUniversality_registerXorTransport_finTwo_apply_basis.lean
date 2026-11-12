-- Prove2me | solution 1 for QEC.Distillation.FiniteRegisterUniversality.registerXorTransport_finTwo_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:16:38.923712+00:00
-- url     : https://prove2.me/submissions/2f73cb43-0cb8-46f6-bc10-0a078849a9a3

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_registerXorBitstring_finTwo
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_apply_basis



set_option autoImplicit false
noncomputable section
universe u
open QEC
open QEC.Distillation
open QEC.Distillation.FiniteRegisterUniversality
open Semantics Semantics.Qubit
open GeneratedUniversality
open scoped Kronecker
variable {Wire : Type u} [Fintype Wire] [DecidableEq Wire]
namespace QEC.Distillation.FiniteRegisterUniversality
theorem _root_.solution (bits : Bitstring (Fin 2)) :
    registerXorTransport (0 : Fin 2) 1 (by decide)
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits) =
      TwoQubit.xorTransport
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits) := by
  rw [registerXorTransport_apply_basis, TwoQubit.xorTransport_apply_basis,
    registerXorBitstring_finTwo]
end QEC.Distillation.FiniteRegisterUniversality
