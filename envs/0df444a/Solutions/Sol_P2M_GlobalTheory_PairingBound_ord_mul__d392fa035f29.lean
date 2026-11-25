-- Prove2me | solution 1 for P2M_GlobalTheory_PairingBound_ord_mul__d392fa035f29
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:31:13.044469+00:00
-- url     : https://prove2.me/submissions/3535df54-023a-4d9c-af39-1e60c808c1c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodDenominatorBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.PairingBound
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]
namespace GlobalTheory.PairingBound
theorem _root_.solution {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : ord_vw O (a * b) = ord_vw O a + ord_vw O b := by
  unfold ord_vw
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb), neg_add]
end GlobalTheory.PairingBound
