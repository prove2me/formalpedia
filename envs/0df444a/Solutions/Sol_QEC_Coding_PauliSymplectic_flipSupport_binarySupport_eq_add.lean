-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.flipSupport_binarySupport_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:44:34.337713+00:00
-- url     : https://prove2.me/submissions/410001a1-d694-41f5-b856-010dc226cc4e

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Theorems.Thm_QEC_Coding_PauliSymplectic_bitstringWordEquiv_eq_self

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PauliSymplectic
open Semantics
universe u
variable {J : Type u} [Fintype J] [DecidableEq J]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution (x y : Word (ZMod 2) J) :
    Qubit.flipSupport (binarySupport x) y = y + x := by
  have h := bitstringWordEquiv_flipSupport x y
  erw [bitstringWordEquiv_eq_self, bitstringWordEquiv_eq_self] at h
  exact h
end QEC.Coding.PauliSymplectic
