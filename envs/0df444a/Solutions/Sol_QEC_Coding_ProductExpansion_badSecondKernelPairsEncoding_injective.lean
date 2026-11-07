-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.badSecondKernelPairsEncoding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:24:34.018588+00:00
-- url     : https://prove2.me/submissions/8880cea1-8046-4445-b8de-57ee13b8ee02

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
omit [Fintype F] [DecidableEq W] hRFinite hR'Finite
namespace QEC.Coding.ProductExpansion
theorem _root_.solution (d : Nat) :
    Function.Injective
      (badSecondKernelPairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d) := by
  intro p q hpq
  apply Subtype.ext
  exact Prod.ext
    (congrArg (fun z => z.1) hpq)
    (congrArg (fun z => z.2.1) hpq)
end QEC.Coding.ProductExpansion
