-- Prove2me | solution 1 for Reformulated.AutPerF.AcrisZero.map_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:53:20.297541+00:00
-- url     : https://prove2.me/submissions/4303e69c-5fbd-4fc3-ab6a-0a2886bdb823

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
import Theorems.Thm_Reformulated_AutPerF_AinfInv_map_frob
import Theorems.Thm_Reformulated_AutPerF_Ainf_map_frob


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
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]
variable {p}
open Reformulated.AutPerF.AcrisZero
namespace Reformulated.AutPerF.AcrisZero
theorem _root_.solution (f : R →+* S) (x : AcrisZero p R) :
    map p f (frob p R x) = frob p S (map p f x) :=
  Subtype.ext (AinfInv.map_frob f _)
end Reformulated.AutPerF.AcrisZero
