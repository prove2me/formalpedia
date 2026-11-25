-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.det_second_cayley_block_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:45.642456+00:00
-- url     : https://prove2.me/submissions/4a14478c-a316-4147-a422-4e72e4cbdc8c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_second_cayley_block_mul_conjTranspose_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_posDef_lower

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
theorem _root_.solution {g : M2 n} (hg : InG g) : (u2 g).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (second_cayley_block_mul_conjTranspose_eq hg)
  rw [det_mul, h, zero_mul] at h1
  exact (posDef_lower hg).det_pos.ne' h1.symm
end PositivityTheory.Rg.Sw.LVs
