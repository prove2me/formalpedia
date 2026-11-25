-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.embOn_single_pf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:06.087813+00:00
-- url     : https://prove2.me/submissions/206d63f2-4641-474d-8bd9-626b3b7326d7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_DerivProdRangeSubMulProdNeZero

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.HSt
theorem _root_.solution (s : Finset (Fin n)) (a b : s) :
    embOn s (Matrix.single a b (1 : ℂ)) = Matrix.single (a : Fin n) (b : Fin n) 1 := by
  ext i j
  by_cases hi : i = (a : Fin n) <;> by_cases hj : j = (b : Fin n)
  · subst hi hj
    simp [embOn, Matrix.single_apply]
  · simp only [embOn, Matrix.single_apply, hj, and_false, if_false]
    split_ifs with h h' <;> simp_all [Subtype.ext_iff]
  · simp only [embOn, Matrix.single_apply, hi, false_and, if_false]
    split_ifs with h h' <;> simp_all [Subtype.ext_iff]
  · simp only [embOn, Matrix.single_apply, hi, false_and, if_false]
    split_ifs with h h' <;> simp_all [Subtype.ext_iff]
end PositivityTheory.Rg.Sw.HSt
