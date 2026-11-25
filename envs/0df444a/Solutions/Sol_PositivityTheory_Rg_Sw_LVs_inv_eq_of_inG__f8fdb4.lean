-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.inv_eq_of_inG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:30.901774+00:00
-- url     : https://prove2.me/submissions/970b1fcd-53f9-4b7f-bba6-e33b9cfe5159

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
theorem _root_.solution {g : M2 n} (hg : InG g) : g⁻¹ = -(JJ n) * gᴴ * JJ n := by
  have h1 : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
    have : -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
    rw [this, hg, Matrix.neg_mul, JJ_mul_JJ, neg_neg]
  exact Matrix.inv_eq_left_inv h1
end PositivityTheory.Rg.Sw.LVs
