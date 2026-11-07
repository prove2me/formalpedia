-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.badChecksForDistanceEncoding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:01:02.741554+00:00
-- url     : https://prove2.me/submissions/bbd1e174-d5b8-40e0-8bdd-88b4f31ce7fa

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
theorem _root_.solution (d : Nat) :
    Function.Injective
      (badChecksForDistanceEncoding (F := F) (W := W) (R := R) d) := by
  intro h g heq
  apply Subtype.ext
  exact congrArg (fun z => z.2.1) heq
end QEC.Coding.ProductExpansion
