-- Prove2me | solution 1 for P2M_Reformulated_AutPerF_eval__mem_map_of_evalOne_bfbf0b8937ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:59.502226+00:00
-- url     : https://prove2.me/submissions/8602f325-0dcb-4383-b841-0c3939fad9d3

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Theorems.Thm_Reformulated_AutPerF_Ainf_ofWitt_teichmuller
import Theorems.Thm_Reformulated_AutPerF_fracWittLift_algebraMap
import Theorems.Thm_Reformulated_AutPerF_AinfInv_liftFracWitt_algebraMap
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap


attribute [local simp] Reformulated.AutPerF.Ainf.ofWitt_teichmuller
attribute [local simp] Reformulated.AutPerF.fracWittLift_algebraMap
attribute [local simp] Reformulated.AutPerF.AinfInv.liftFracWitt_algebraMap

set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
variable [IsAdicComplete (span {(p : R)}) R]
namespace Reformulated.AutPerF
theorem _root_.solution {A : Type*} [CommRing A] (I : Ideal A) {y : AdicCompletion I A}
    (hy : AdicCompletion.evalOneₐ I y = 0) (n : ℕ) :
    AdicCompletion.evalₐ I n y ∈ I.map (Ideal.Quotient.mk (I ^ n)) := by
  rcases n with _ | n
  · rw [Subsingleton.elim
      (h := Ideal.Quotient.subsingleton_iff.2 (by simp)) (AdicCompletion.evalₐ I 0 y) 0]
    exact zero_mem _
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
  have h1 := factorPow_evalₐ I (show 1 ≤ n + 1 by omega) y
  rw [← AdicCompletion.factorₐ_evalₐ_one, ← h1, ← ha] at hy
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    Ideal.Quotient.eq_zero_iff_mem] at hy
  rw [← ha]
  exact Ideal.mem_map_of_mem _ hy
end Reformulated.AutPerF
