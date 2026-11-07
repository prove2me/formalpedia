-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.badBidirectionalLocalPairsEncoding_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:24:54.520214+00:00
-- url     : https://prove2.me/submissions/994284a2-e5d0-4d5a-b784-83df4b681370

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (d s m k : Nat)
    (p : badBidirectionalLocalPairs
      (F := F) (W := W) (R := R) (R' := R') d s m k) :
    badBidirectionalLocalPairsSumVal
      (badBidirectionalLocalPairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d s m k p) = p.1 := by
  classical
  unfold badBidirectionalLocalPairsEncoding
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl
end QEC.Coding.ProductExpansion
