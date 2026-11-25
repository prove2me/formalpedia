-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.eval_eq_zero_of_mem_ker_theta_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:50:43.116584+00:00
-- url     : https://prove2.me/submissions/1d5b7dbf-d8cd-4565-96a6-6c3b3809b438

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Theorems.Thm_P2M_Reformulated_AutPerF_eval__mem_map_of_evalOne_bfbf0b8937ef
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_theta_eq_zero_iff


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
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
variable [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.BdRPlus
variable {p}
namespace Reformulated.AutPerF.BdRPlus
theorem _root_.solution {n : ℕ} {x : BdRPlus p R} (hx : x ∈ fil p R n) :
    eval p R n x = 0 := by
  have h1 : RingHom.ker (theta p R) ≤
      ((AinfInv.kerTheta p R).map (Ideal.Quotient.mk (AinfInv.kerTheta p R ^ n))).comap
        (eval p R n) := by
    intro y hy
    rw [RingHom.mem_ker, theta_eq_zero_iff] at hy
    exact evalₐ_mem_map_of_evalOne _ hy n
  have h2 := pow_le_comap_pow h1 n hx
  rw [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_comap, Ideal.mem_bot] at h2
  exact h2
end Reformulated.AutPerF.BdRPlus
