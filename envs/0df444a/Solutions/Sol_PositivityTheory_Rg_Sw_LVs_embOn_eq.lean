-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.embOn_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:09.154828+00:00
-- url     : https://prove2.me/submissions/0d739580-ffe9-4db8-9b9c-6e281f063264

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_sum_incl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (s : Finset (Fin n)) (T : Matrix s s ℂ) : embOn s T = incl s * T * (incl s)ᵀ := by
  ext a b
  simp only [Matrix.mul_apply, incl, Matrix.of_apply, Matrix.transpose_apply]
  simp only [sum_incl]
  simp only [mul_comm _ (ite (b = _) _ _)]
  rw [sum_incl]
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;> simp [embOn, ha, hb]
end PositivityTheory.Rg.Sw.LVs
