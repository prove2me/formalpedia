-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.scalar_section_mul_conjugate_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:26.289064+00:00
-- url     : https://prove2.me/submissions/44355662-6d62-4f8b-af74-cd8795ffdb63

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_first_cayley_block_ne_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_second_cayley_block_ne_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_first_cayley_block_unitary
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inverse_first_block_eq_of_group


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
theorem _root_.solution {k : M2 n} (hk : InK k) (p q : ℤ) : f0 p q k * fV p q k = 1 := by
  have h1 := det_first_cayley_block_ne_zero hk.1
  have h2 := det_second_cayley_block_ne_zero hk.1
  have hs : (u1 k).det * star (u1 k).det = 1 := by
    have := congrArg Matrix.det (first_cayley_block_unitary hk)
    rwa [det_mul, det_conjTranspose, det_one] at this
  have hs' : star (u1 k).det ≠ 0 := star_ne_zero.2 h1
  rw [f0, fV, inverse_first_block_eq_of_group hk.1, det_conjTranspose]
  have e : (u1 k).det ^ (-p) * (u2 k).det ^ (-q) * ((u1 k).det ^ (p - n) * (u2 k).det ^ q * star (u1 k).det ^ (-(n : ℤ)))
      = ((u1 k).det ^ (-p) * (u1 k).det ^ (p - n)) * ((u2 k).det ^ (-q) * (u2 k).det ^ q) *
        star (u1 k).det ^ (-(n : ℤ)) := by ring
  rw [e, ← zpow_add₀ h1, ← zpow_add₀ h2, show -p + (p - (n : ℤ)) = -(n : ℤ) by ring, show -q + q = 0 by ring,
    zpow_zero, mul_one, ← mul_zpow, hs, _root_.one_zpow]
end PositivityTheory.Rg.Sw.LVs
