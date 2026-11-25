-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.rcp_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:53.86658+00:00
-- url     : https://prove2.me/submissions/bdf5ea75-d9fe-4628-8610-4d2889b39593

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDiv
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_opH_rcp
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_rcp_add
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_rcp_comp


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
theorem _root_.solution (s : ℂ) (m : ℕ) {T : Module.End ℂ (Fm n)} (hT : T ∈ Algebra.adjoin ℂ (Sop s m n)) : RCP T := by
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact opH_rcp s m _ _ _
  | algebraMap r =>
    intro R q
    simp only [Module.algebraMap_end_apply, smul_mul_assoc]
  | add x y _ _ hx hy => exact rcp_add hx hy
  | mul x y _ _ hx hy => rw [Module.End.mul_eq_comp]; exact rcp_comp hx hy
end PositivityTheory.Rg.Sw.SP
