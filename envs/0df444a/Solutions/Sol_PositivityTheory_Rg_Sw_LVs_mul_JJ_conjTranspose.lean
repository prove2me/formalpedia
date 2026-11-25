-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.mul_JJ_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:38.328424+00:00
-- url     : https://prove2.me/submissions/1eee1068-ce55-467c-b446-20935b05d3e3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_JJ_mul_JJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {g : M2 n} (hg : InG g) : g * JJ n * gᴴ = JJ n := by
  have h1 : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
    have : -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
    rw [this, hg, Matrix.neg_mul, JJ_mul_JJ, neg_neg]
  have h2 : g * (-(JJ n) * gᴴ * JJ n) = 1 := mul_eq_one_comm.1 h1
  have h3 : g * (-(JJ n) * gᴴ * JJ n) * JJ n = JJ n := by rw [h2, Matrix.one_mul]
  have h4 : g * (-(JJ n) * gᴴ * JJ n) * JJ n = g * JJ n * gᴴ := by
    simp only [Matrix.mul_assoc, JJ_mul_JJ, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, neg_neg]
  rw [← h4, h3]
end PositivityTheory.Rg.Sw.LVs
