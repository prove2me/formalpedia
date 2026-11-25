-- Prove2me | solution 1 for PI.Dv.TIW.abs_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:06:59.284539+00:00
-- url     : https://prove2.me/submissions/2c157b28-bde1-4b59-b040-7f0f6990ac24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Theorems.Thm_PI_Dv_TIW_norm_embedding_eq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped WithZero
namespace PI.Dv.TIW
theorem _root_.solution {K : Type} [Field K] [NumberField K] (x : 𝓞 K) (B : ℝ) (hB : 0 ≤ B)
    (hσ : ∀ σ : K →+* ℂ, ‖σ (algebraMap (𝓞 K) K x)‖ ≤ B) :
    |((Algebra.norm ℤ x : ℤ) : ℝ)| ≤ B ^ Module.finrank ℚ K := by
  have h1 : |((Algebra.norm ℤ x : ℤ) : ℝ)| =
      ∏ w : InfinitePlace K, w (algebraMap (𝓞 K) K x) ^ w.mult := by
    rw [InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int]
    first
    | simp
    | norm_cast
  rw [h1, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun w _ => pow_nonneg (AbsoluteValue.nonneg _ _) _) (fun w _ => ?_)
  refine pow_le_pow_left₀ (AbsoluteValue.nonneg _ _) ?_ _
  rw [← InfinitePlace.norm_embedding_eq]
  exact hσ _
end PI.Dv.TIW
