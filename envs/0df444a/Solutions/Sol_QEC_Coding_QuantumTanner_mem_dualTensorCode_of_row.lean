-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.mem_dualTensorCode_of_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:08:15.807796+00:00
-- url     : https://prove2.me/submissions/c73fa7a3-b5b3-4c6d-9d07-b921849b4a2a

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_QuantumTanner_Core

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
namespace QEC.Coding.QuantumTanner
theorem _root_.solution {F : Type u} {A B : Type v} [Field F] [Fintype F]
    [Fintype A] [Fintype B] (CA : LinearCode F A) (CB : LinearCode F B)
    {x : Word F (A × B)} (hx : ∀ a, rowRestriction a x ∈ CB.carrier) :
    x ∈ (dualTensorCode CA CB).carrier := by
  exact Submodule.mem_sup_right hx
end QEC.Coding.QuantumTanner
