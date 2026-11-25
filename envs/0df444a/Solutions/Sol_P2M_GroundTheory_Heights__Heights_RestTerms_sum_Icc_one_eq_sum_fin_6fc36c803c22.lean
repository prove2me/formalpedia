-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_sum_Icc_one_eq_sum_fin_6fc36c803c22
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:13:33.307751+00:00
-- url     : https://prove2.me/submissions/70c27b5d-706e-4c5d-8a92-6f9ce2dc6347

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagPowerSumPreimage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → M) :
    ∑ l ∈ Finset.Icc 1 N, g l = ∑ i : Fin N, g (i.val + 1) := by
  have hI : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [Fin.sum_univ_eq_sum_range (fun i => g (i + 1)), hI, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  exact Finset.sum_congr rfl (fun i _ => by rw [add_comm])
end GroundTheory.Heights₂.Heights.RestTerms
