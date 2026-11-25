-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.ker_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:54:16.003617+00:00
-- url     : https://prove2.me/submissions/285934f8-f364-46d9-80ef-7b86898d7002

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_mem_span_of_approx
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_xi
import Theorems.Thm_Reformulated_AutPerF_Ainf_exists_eq_xi_mul_add
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


attribute [local simp] Reformulated.AutPerF.Ainf.theta_xi

set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Ainf
variable [IsDomain R]
variable [ValuationRing R]
variable [CharZero R]
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution (ϖ : PFlat p R) : RingHom.ker (theta p R) = span {xi ϖ} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · refine mem_span_of_approx (p : Ainf p R) (xi ϖ) (RingHom.ker (theta p R)) ?_ hx
    intro x hx
    have hx' : theta p R x = 0 := hx
    obtain ⟨a, y, h⟩ := exists_eq_xi_mul_add ϖ (x := x) (by rw [hx']; exact dvd_zero _)
    refine ⟨a, y, ?_, h⟩
    rw [h] at hx'
    simpa [(Fact.out : p.Prime).ne_zero] using hx'
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact theta_xi ϖ
end Reformulated.AutPerF.Ainf
