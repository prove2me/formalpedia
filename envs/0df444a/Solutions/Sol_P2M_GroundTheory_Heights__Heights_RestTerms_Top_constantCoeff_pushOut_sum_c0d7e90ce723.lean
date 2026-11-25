-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_pushOut_sum_c0d7e90ce723
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:36:18.915061+00:00
-- url     : https://prove2.me/submissions/7f7afc8f-637a-4484-880f-cf2387439949

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_pushOut_41e75ddda8c4

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
theorem _root_.solution (r a : ℕ) (c : SmallBlock) (κ : ℚ) (s : Finset (Fin r → ℕ))
    (hs : ∀ lam ∈ s, Antitone lam) (b : (Fin r → ℕ) → ℚ) :
    constantCoeff (∑ lam ∈ s, b lam • pushOut r a c κ lam) =
      if rectangle r a ∈ s then b (rectangle r a) * κ else 0 := by
  rw [map_sum]
  have : ∀ lam ∈ s, constantCoeff (b lam • pushOut r a c κ lam) =
      if lam = rectangle r a then b lam * κ else 0 := by
    intro lam hlam
    rw [smul_eq_C_mul, map_mul, constantCoeff_C, constantCoeff_pushOut r a c κ lam (hs lam hlam)]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
end GroundTheory.Heights₂.Heights.RestTerms.Top
