-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.NullPf.rank_lt_of_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:20.37109+00:00
-- url     : https://prove2.me/submissions/3b8a5845-933c-48b4-908f-6b585f903335

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DetEqZeroOfRankLt
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_NullPf_exists_minor_ne_zero

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
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {k : ℕ}
    (h : ∀ I J : Fin k ↪ Fin n, (M.submatrix I J).det = 0) : M.rank < k := by
  by_contra hc
  obtain ⟨I, J, hIJ⟩ := exists_minor_ne_zero M (not_lt.1 hc)
  exact hIJ (h I J)
end PositivityTheory.Rg.Sw.SP.NullPf
