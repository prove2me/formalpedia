-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.rot_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:36.454588+00:00
-- url     : https://prove2.me/submissions/126dbe45-3c9c-4f44-bc4b-5b86ce712f82

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_StarExpNegI
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_exp_neg_I
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_rot_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_dA_ne
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_dB_ne
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_smul_conjCm
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_conj_nU


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
theorem _root_.solution (j : ℕ) (θ : ℝ) (r s : Fin n) :
    Complex.exp (2 * θ * Complex.I) • (rot j θ * nU (single r s 1) * (rot j θ)⁻¹ - 1) =
      Cm n * (zLow j r s + Complex.exp (2 * θ * Complex.I) • zMid j r s +
        Complex.exp (2 * θ * Complex.I) ^ 2 • zTop j r s) * CmI n := by
  rw [rot_eq, conj_nU _ _ (dA_ne j θ) (dB_ne j θ), smul_conjCm]
  congr 2
  have he : Complex.exp (2 * θ * Complex.I) = Complex.exp (θ * Complex.I) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hu0 : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  rw [he]
  simp only [dA, dB, zLow, zMid, zTop, blkB, Finset.mem_compl, exp_neg_I]
  by_cases hr : r ∈ blkA j <;> by_cases hs : s ∈ blkA j <;>
    simp [hr, hs, fromBlocks_smul, fromBlocks_add, fromBlocks_neg, smul_single, fromBlocks_inj]
  all_goals constructor <;> congr 1 <;> field_simp <;> ring
end PositivityTheory.Rg.Sw.LVs.TC
