-- Prove2me | solution 1 for PositivityTheory.KReal.ne_zero_of_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:25:31.271035+00:00
-- url     : https://prove2.me/submissions/4ba50900-5042-4298-8eb1-e5ba99028a95

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Theorems.Thm_P2M_PositivityTheory_KReal_genG_le__7406e1e366d6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {r s : ℕ} {T : Type} [AddCommGroup T] [Module ℂ T] [Nontrivial T]
    (act : Mat r s →ₗ[ℂ] Module.End ℂ T) (v : T) (h : genG act (Submodule.span ℂ {v}) = ⊤) : v ≠ 0 := by
  rintro rfl
  have : genG act (Submodule.span ℂ {(0 : T)}) ≤ ⊥ := by
    refine genG_le' (by simp) fun W x hx => ?_
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]
  rw [h] at this
  exact top_ne_bot (le_bot_iff.1 this)
end PositivityTheory.KReal
