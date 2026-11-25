-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.NullPf.det_eq_zero_of_rank_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:49:01.313749+00:00
-- url     : https://prove2.me/submissions/2a69c07a-5afd-4acb-862b-855d9e09d57d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DetEqZeroOfRankLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Module
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.SP.NullPf
variable {K : Type*} [Field K]
namespace PositivityTheory.Rg.Sw.SP.NullPf
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : M.rank < n) : M.det = 0 := by
  by_contra hd
  have := Matrix.rank_of_isUnit M ((Matrix.isUnit_iff_isUnit_det M).2 (Ne.isUnit hd))
  simp at this
  omega
end PositivityTheory.Rg.Sw.SP.NullPf
