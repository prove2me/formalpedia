-- Prove2me | solution 1 for Reformulated.AutPerF.BdR.mem_fil_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:14:27.419402+00:00
-- url     : https://prove2.me/submissions/66bccfe2-e781-4d21-afd6-3032f0af3baa

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_xi
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Ainf.theta_xi
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap



set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R]
open Reformulated.AutPerF.BdR
variable [IsAlgClosed (FractionRing R)]
variable {π : BdRPlus p R} (hπ : RingHom.ker (BdRPlus.theta p R) = span {π})
include hπ
namespace Reformulated.AutPerF.BdR
theorem _root_.solution (i : ℤ) (x : BdR p R) : x ∈ fil p R i ↔ ∃ c : BdRPlus p R,
    x = algebraMap (BdRPlus p R) (BdR p R) π ^ i * algebraMap (BdRPlus p R) (BdR p R) c := by
  rw [fil_eq_span hπ, Submodule.mem_span_singleton]
  simp only [Algebra.smul_def, mul_comm, eq_comm]
end Reformulated.AutPerF.BdR
