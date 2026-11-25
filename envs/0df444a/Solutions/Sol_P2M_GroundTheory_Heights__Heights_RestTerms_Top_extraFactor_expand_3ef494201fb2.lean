-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_extraFactor_expand_3ef494201fb2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:47.094886+00:00
-- url     : https://prove2.me/submissions/10826739-db6f-45c9-b6f3-b986d3851660

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_schur_zero_cf6b31ecc1ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_partitionsOf_zero_1c112b433a02

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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (hF : FrobeniusCharacterFormula.Statement) (r q m : ℕ) :
    extraFactor r q * psum (Fin r) ℚ 1 ^ m =
      ∑ lam ∈ partitionsOf r (q + m), C (blockCoeff q m lam) * schur (Fin r) lam := by
  unfold extraFactor blockCoeff
  by_cases hq : q = 0
  · subst hq
    simp only [if_true, one_mul, zero_add]
    by_cases hm : m = 0
    · subst hm
      simp [partitionsOf_zero, schur_zero]
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have := hF r 1 m' le_rfl
      rw [pow_succ', this, add_comm 1 m']
      refine Finset.sum_congr rfl fun lam _ => ?_
      rw [if_neg hm, List.replicate_succ]
  · simp only [if_neg hq]
    exact hF r q m (Nat.one_le_iff_ne_zero.mpr hq)
end GroundTheory.Heights₂.Heights.RestTerms.Top
