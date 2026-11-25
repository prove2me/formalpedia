-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_esymm_mem_range_4f4cf4a0cb66
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:34.054092+00:00
-- url     : https://prove2.me/submissions/1b18778c-d32c-4048-bd1f-6986a67ab0e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_psum_mem_range_c0a256d7f214

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
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (N k : ℕ) (hk : k ≤ N) :
    esymm (Fin N) ℚ k ∈ (powerSumHom N).range := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [esymm_zero]; exact Subalgebra.one_mem _
    have hN := mul_esymm_eq_sum (Fin N) ℚ k
    have hmem : (k : MvPolynomial (Fin N) ℚ) * esymm (Fin N) ℚ k ∈ (powerSumHom N).range := by
      rw [hN]
      refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _) ?_
      refine Subalgebra.sum_mem _ (fun a ha => ?_)
      obtain ⟨ha1', ha2⟩ := Finset.mem_filter.mp ha
      have ha1 := Finset.HasAntidiagonal.mem_antidiagonal.mp ha1'
      refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _
        (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _)
        (ih a.1 ha2 (by omega))) (psum_mem_range N a.2 (by omega) (by omega))
    have hinv : esymm (Fin N) ℚ k = C ((k : ℚ)⁻¹) * ((k : MvPolynomial (Fin N) ℚ) * esymm (Fin N) ℚ k) := by
      rw [← mul_assoc, show (k : MvPolynomial (Fin N) ℚ) = C (k : ℚ) by simp, ← C_mul,
        inv_mul_cancel₀ (by exact_mod_cast hk0.ne'), C_1, one_mul]
    rw [hinv]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hmem
end GroundTheory.Heights₂.Heights.RestTerms.Flag
