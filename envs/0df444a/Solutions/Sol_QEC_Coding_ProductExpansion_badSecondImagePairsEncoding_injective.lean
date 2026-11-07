-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.badSecondImagePairsEncoding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:24:42.165596+00:00
-- url     : https://prove2.me/submissions/7d882ea3-7453-4087-bbcf-365aebfd3266

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
omit [Fintype F] [DecidableEq W] hRFinite
namespace QEC.Coding.ProductExpansion
theorem _root_.solution (d : Nat) :
    Function.Injective
      (badSecondImagePairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d) := by
  intro p q hpq
  apply Subtype.ext
  exact Prod.ext
    (congrArg (fun z => z.1) hpq)
    (congrArg (fun z => z.2.1) hpq)
end QEC.Coding.ProductExpansion
