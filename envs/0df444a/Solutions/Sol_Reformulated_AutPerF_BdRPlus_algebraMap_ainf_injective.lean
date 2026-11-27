-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.algebraMap_ainf_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:32:35.196395+00:00
-- url     : https://prove2.me/submissions/b695c3dc-b344-4889-9cae-7f811fddd8e5

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
import Theorems.Thm_Reformulated_AutPerF_AinfInv_algebraMap_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R]
open Reformulated.AutPerF.BdRPlus
variable [IsAlgClosed (FractionRing R)]
namespace Reformulated.AutPerF.BdRPlus
theorem _root_.solution : Function.Injective (algebraMap (Ainf p R) (BdRPlus p R)) :=
  algebraMap_injective.comp AinfInv.algebraMap_injective
end Reformulated.AutPerF.BdRPlus
