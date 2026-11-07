-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.parityCheckCode_generatorImageParityCheck_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:01:59.035195+00:00
-- url     : https://prove2.me/submissions/23ab4abf-bf5f-47e8-bd0d-fcf38d1efc8d

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [DecidableEq F] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (g : Matrix R W F) :
    (parityCheckCode (generatorImageParityCheck g)).carrier = generatorImage g := by
  classical
  unfold parityCheckCode generatorImageParityCheck
  rw [Matrix.toLin'_toMatrix', Submodule.ker_projection]
end QEC.Coding.ProductExpansion
