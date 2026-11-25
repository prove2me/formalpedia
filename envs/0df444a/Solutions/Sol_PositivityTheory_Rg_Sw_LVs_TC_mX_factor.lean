-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.mX_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:20:56.860921+00:00
-- url     : https://prove2.me/submissions/5fcd17bb-44f5-4d0c-89bf-68aff2502be7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatA
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlkB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatB
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_mul_compl_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_cmI_mul_cm
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_cm_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution (j : ℕ) (P Q R S : Matrix (Fin n) (Fin n) ℂ) (hP : ∀ a b, P a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j)
    (hS : ∀ a b, S a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) (hQ : ∀ a b, Q a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkA j)
    (hR : ∀ a b, R a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkB j) :
    mX (1 + P) Q R (1 + S) = mX 1 Q R 1 * mX (1 + P) 0 0 (1 + S) := by
  have hQS : Q * S = 0 := mul_compl_zero j Q S (fun a b h => (hQ a b h).2) (fun a b h => (hS a b h).1)
  have hRP : R * P = 0 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hr : R a k = 0
    · simp [hr]
    by_cases hp : P k b = 0
    · simp [hp]
    exact absurd (hP k b hp).1 (by have := (hR a k hr).2; simp [blkB] at this; exact this)
  unfold mX
  rw [cm_inv, show Cm n * fromBlocks 1 Q R 1 * CmI n * (Cm n * fromBlocks (1 + P) 0 0 (1 + S) * CmI n) =
      Cm n * (fromBlocks 1 Q R 1 * (CmI n * Cm n) * fromBlocks (1 + P) 0 0 (1 + S)) * CmI n by
        simp only [Matrix.mul_assoc], cmI_mul_cm, Matrix.mul_one, fromBlocks_multiply]
  simp [Matrix.mul_add, hQS, hRP]
end PositivityTheory.Rg.Sw.LVs.TC
