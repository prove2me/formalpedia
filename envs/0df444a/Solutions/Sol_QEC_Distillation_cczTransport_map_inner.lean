-- Prove2me | solution 1 for QEC.Distillation.cczTransport_map_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:17:23.00583+00:00
-- url     : https://prove2.me/submissions/ebcc0920-97b6-40c1-8f47-8de2ee973dc6

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
universe u
variable {F ι : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
namespace QEC.Distillation
theorem _root_.solution
    (psi chi : EuclideanSpace Complex (F × F × F)) :
    inner Complex (cczTransport psi) (cczTransport chi) = inner Complex psi chi :=
  cczDiagonalOperator_map_inner psi chi
end QEC.Distillation
