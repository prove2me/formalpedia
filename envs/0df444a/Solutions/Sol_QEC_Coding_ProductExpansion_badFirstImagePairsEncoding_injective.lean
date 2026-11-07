-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.badFirstImagePairsEncoding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:24:33.042201+00:00
-- url     : https://prove2.me/submissions/71db2330-eb0c-47c1-a104-288379078b84

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
omit [Fintype F] [DecidableEq W] hR'Finite
namespace QEC.Coding.ProductExpansion
theorem _root_.solution (d : Nat) :
    Function.Injective
      (badFirstImagePairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d) := by
  intro p q hpq
  apply Subtype.ext
  exact Prod.ext
    (congrArg (fun z => z.1.1) hpq)
    (congrArg (fun z => z.2) hpq)
end QEC.Coding.ProductExpansion
