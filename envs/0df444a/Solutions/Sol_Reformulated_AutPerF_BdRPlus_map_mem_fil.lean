-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.map_mem_fil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:20:36.247655+00:00
-- url     : https://prove2.me/submissions/ff741331-7e4a-4e65-b2ba-271cd815d3d7

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap
import Theorems.Thm_Reformulated_AutPerF_AinfInv_theta_map
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_map


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
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]
open Reformulated.AutPerF.BdRPlus
variable {p}
namespace Reformulated.AutPerF.BdRPlus
theorem _root_.solution (f : R →+* S) {n : ℕ} {x : BdRPlus p R} (hx : x ∈ fil p R n) :
    map p f x ∈ fil p S n :=
  pow_le_comap_pow (I := RingHom.ker (theta p R)) (J := RingHom.ker (theta p S)) (f := map p f)
    (fun y hy => by
      rw [Ideal.mem_comap, RingHom.mem_ker, theta_map, RingHom.mem_ker.1 hy, map_zero]) n hx
end Reformulated.AutPerF.BdRPlus
