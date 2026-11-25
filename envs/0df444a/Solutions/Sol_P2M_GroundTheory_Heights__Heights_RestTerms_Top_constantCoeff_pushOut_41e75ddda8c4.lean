-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_pushOut_41e75ddda8c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:53.133871+00:00
-- url     : https://prove2.me/submissions/9a06c7ce-cab9-4bfc-861a-02a81e34f04e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_schur_zero_cf6b31ecc1ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_schur_d5169a16bac0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_aeval_of_zero_d253147093f5

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
theorem _root_.solution (r a : ℕ) (c : SmallBlock) (κ : ℚ) (lam : Fin r → ℕ)
    (hl : Antitone lam) :
    constantCoeff (pushOut r a c κ lam) = if lam = rectangle r a then κ else 0 := by
  unfold pushOut
  split_ifs with h1 h2 h2
  · subst h2
    have : (fun i : Fin r => rectangle r a i - a) = 0 := funext fun i => by simp [rectangle]
    rw [map_mul, constantCoeff_C, xSign, constantCoeff_aeval_of_zero _ (fun i => by simp), this,
      schur_zero, map_one, mul_one]
  · rw [map_mul, constantCoeff_C, xSign, constantCoeff_aeval_of_zero _ (fun i => by simp),
      constantCoeff_schur _ _ (fun i j hij => Nat.sub_le_sub_right (hl hij) a), if_neg, mul_zero]
    intro h0
    exact h2 (funext fun i => by
      have := congrFun h0 i
      simp only [Pi.zero_apply] at this
      have := h1 i
      simp [rectangle]; omega)
  · exact absurd (fun i => by rw [h2]; simp [rectangle]) h1
  · simp
end GroundTheory.Heights₂.Heights.RestTerms.Top
