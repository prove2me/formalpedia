-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.yv_true_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:52.338243+00:00
-- url     : https://prove2.me/submissions/f9bfc752-cf0f-49c3-840c-174b84201fce

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (i j : Fin n) : yv true i j ∈ AT n := Algebra.subset_adjoin ⟨(i, j), rfl⟩
end PositivityTheory.Rg.Sw.SP
