-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchurSignCoefficient_proof_567c051d0467
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:04.17542+00:00
-- url     : https://prove2.me/submissions/dd7c328a-24e2-4d50-a902-abfbc83c04a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchurSignCoefficient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchurSignCoefficient_coeff_aeval_diagonal_0e15d31de021
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchurSignCoefficient_aeval_smul_powerSumHom_dece80d62ad1

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
namespace SchurSignCoefficient
theorem _root_.solution (h : SchurPowerSumCoefficient.Statement) :
    SchurSignCoefficient.Statement := by
  intro N r k hk1 hkN nu s _ hnu hsum
  obtain ⟨S₀, hS₀, hc₀⟩ := h N r k hk1 hkN nu hnu hsum
  refine ⟨aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i) S₀, ?_, ?_⟩
  · rw [← SchurSignCoefficient.aeval_smul_powerSumHom, hS₀]
  · rw [SchurSignCoefficient.coeff_aeval_diagonal, hc₀]
    congr 1
    rw [Finset.prod_eq_single (⟨k - 1, by omega⟩ : Fin N)]
    · rw [Finsupp.single_eq_same, pow_one]
      congr 1
      simp only
      omega
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg (Ne.symm hb), pow_zero]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
end SchurSignCoefficient
end GroundTheory.Heights₂.Heights.RestTerms
