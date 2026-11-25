-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.wM_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:26.727353+00:00
-- url     : https://prove2.me/submissions/b57020e2-d9a1-462b-91a9-31379e89461a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_first_cayley_block_unitary
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_second_cayley_block_unitary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {k : M2 n} (hk : InK k) : wM k ∈ unitaryGroup (Fin n) ℂ := by
  have h1 : u1 k ∈ unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff.2 (first_cayley_block_unitary hk)
  have h2 : u2 k ∈ unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff.2 (second_cayley_block_unitary hk)
  have hi : (u2 k)⁻¹ = star (u2 k) := Matrix.inv_eq_right_inv (second_cayley_block_unitary hk)
  rw [wM, hi]
  exact Submonoid.mul_mem _ (Matrix.mem_unitaryGroup_iff.2 (by rw [star_star]; exact Matrix.mem_unitaryGroup_iff'.1 h2)) h1
end PositivityTheory.Rg.Sw.LVs
