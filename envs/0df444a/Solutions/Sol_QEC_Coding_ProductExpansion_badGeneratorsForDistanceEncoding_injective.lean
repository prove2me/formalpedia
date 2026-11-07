-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.badGeneratorsForDistanceEncoding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:01:17.50853+00:00
-- url     : https://prove2.me/submissions/e46c96f3-4806-4907-8ac0-98d4960e83bd

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
omit [Fintype F] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution (d : Nat) :
    Function.Injective
      (badGeneratorsForDistanceEncoding (F := F) (W := W) (R := R) d) := by
  intro g f hgf
  apply Subtype.ext
  exact congrArg (fun z => z.2.2.1) hgf
end QEC.Coding.ProductExpansion
