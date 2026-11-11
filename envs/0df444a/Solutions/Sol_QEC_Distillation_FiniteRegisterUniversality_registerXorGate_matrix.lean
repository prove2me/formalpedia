-- Prove2me | solution 1 for QEC.Distillation.FiniteRegisterUniversality.registerXorGate_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:23:34.250857+00:00
-- url     : https://prove2.me/submissions/9a83aa52-b5ea-48cd-b904-f0457ed119aa

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality

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
theorem _root_.solution (control target : Wire)
    (hdistinct : control ≠ target) :
    (registerXorGate control target hdistinct :
      Matrix (Bitstring Wire) (Bitstring Wire) Complex) =
      (registerXorBitstringEquiv control target hdistinct).permMatrix Complex :=
  rfl
end QEC.Distillation.FiniteRegisterUniversality
