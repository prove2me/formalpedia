-- Prove2me | solution 1 for Reformulated.AutPerF.mem_dpSpan_Ici
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:23:43.112538+00:00
-- url     : https://prove2.me/submissions/36a50d5f-17ab-4454-8579-a1d6d5343054

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope
import Theorems.Thm_Reformulated_AutPerF_dpSpan_mono
import Theorems.Thm_Reformulated_AutPerF_dp_mem_dpSpan
import Theorems.Thm_Reformulated_AutPerF_natCast_mul_mem
import Theorems.Thm_Reformulated_AutPerF_exists_eq_of_mem_dpSpan
import Theorems.Thm_Reformulated_AutPerF_pow_dvd_of_mem_dpSpan
import Theorems.Thm_Reformulated_AutPerF_smul_dp_of_eq
import Theorems.Thm_Reformulated_AutPerF_dvd_of_pow_succ_dvd_smul_dp
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap



set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
variable {B : Type*} [CommRing B] [Algebra ℚ B]
variable {A : Type*} [CommRing A] [Algebra A B]
variable {ξ : A}
variable [IsDomain B] (h0 : algebraMap A B ξ ≠ 0)
  (hξ : ∀ a : A, algebraMap A B ξ ∣ algebraMap A B a → ξ ∣ a)
include h0 hξ
namespace Reformulated.AutPerF
theorem _root_.solution {m : ℕ} {z : B} (hz : z ∈ dpSpan B ξ Set.univ)
    (h : algebraMap A B ξ ^ m ∣ z) : z ∈ dpSpan B ξ (Set.Ici m) := by
  induction m with
  | zero => exact dpSpan_mono (fun _ _ => Nat.zero_le _) hz
  | succ m ih =>
    obtain ⟨a, w, hw, rfl⟩ := exists_eq_of_mem_dpSpan (m := m) (t := Set.Ici (m + 1))
      (fun k hk => by simp at hk ⊢; omega) (ih ((pow_dvd_pow _ m.le_succ).trans h))
    have hw' := pow_dvd_of_mem_dpSpan (n := m + 1) (fun _ hk => hk) hw
    obtain ⟨c, rfl⟩ := dvd_of_pow_succ_dvd_smul_dp h0 hξ ((dvd_add_left hw').1 h)
    rw [smul_dp_of_eq]
    exact add_mem (natCast_mul_mem _ (Submodule.smul_mem _ _ (dp_mem_dpSpan (by simp)))) hw
end Reformulated.AutPerF
