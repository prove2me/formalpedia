-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.badChecksForRectangleEncoding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:02:05.416087+00:00
-- url     : https://prove2.me/submissions/bee05516-fed8-47fa-a37c-2503f85e6230

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
omit [Fintype F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h' : Matrix R' W F) (A B : Finset W) (s k : Nat) :
    Function.Injective
      (badChecksForRectangleEncoding (R := R) h' A B s k) := by
  intro h g heq
  apply Subtype.ext
  exact congrArg (fun z => z.2.1) heq
end QEC.Coding.ProductExpansion
