-- Prove2me | solution 1 for QEC.Coding.FiberBundle.multipleRotation_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:18:15.227203+00:00
-- url     : https://prove2.me/submissions/33002440-dc4e-4748-8f18-48d049f7f7ca

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_FiberBundle_Core

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (ell : Nat) [NeZero ell] (k : Fin ell) :
    multipleRotation ell k = (k.val * ell : Nat) := by
  rfl
end QEC.Coding.FiberBundle
