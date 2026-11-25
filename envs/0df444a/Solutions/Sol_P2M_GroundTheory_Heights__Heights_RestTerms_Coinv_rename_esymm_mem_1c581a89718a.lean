-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_rename_esymm_mem_1c581a89718a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:26:02.989966+00:00
-- url     : https://prove2.me/submissions/3eb57310-c6e3-4d9e-adee-5fae9be77088

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoinvReduction
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_bps_mem_psumIdeal_6a4fee1897e0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_rename_psum_aae3244de93b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Coinv
open MvPolynomial Finset
noncomputable section
variable (K : Type*) [Field K] (f n : ℕ)
variable {K f n}
variable [CharZero K]
namespace GroundTheory.Heights₂.Heights.RestTerms.Coinv
theorem _root_.solution {m : ℕ} (b : Fin f) (h1 : 1 ≤ m) (h2 : m ≤ n) :
    rename (fun i : Fin n => (b, i)) (esymm (Fin n) K m) ∈ psumIdeal K f n := by
  have hN := congrArg (rename (fun i : Fin n => (b, i))) (mul_esymm_eq_sum (Fin n) K m)
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_sum] at hN
  have hmem : ((m : ℕ) : MvPolynomial (Fin f × Fin n) K) *
      rename (fun i : Fin n => (b, i)) (esymm (Fin n) K m) ∈ psumIdeal K f n := by
    rw [hN]
    refine Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    have ha1 : a.1 + a.2 = m := by simpa using ha.1
    rw [rename_psum]
    exact Ideal.mul_mem_left _ _ (bps_mem_psumIdeal b (by have := ha.2; omega) (by omega))
  have hm : (m : K) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have : rename (fun i : Fin n => (b, i)) (esymm (Fin n) K m) =
      C ((m : K)⁻¹) * (((m : ℕ) : MvPolynomial (Fin f × Fin n) K) *
        rename (fun i : Fin n => (b, i)) (esymm (Fin n) K m)) := by
    rw [← mul_assoc, ← map_natCast C, ← C_mul, inv_mul_cancel₀ hm, C_1, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ hmem
end GroundTheory.Heights₂.Heights.RestTerms.Coinv
