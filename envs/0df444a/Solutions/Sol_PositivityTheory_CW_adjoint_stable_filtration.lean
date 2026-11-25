-- Prove2me | solution 1 for PositivityTheory.CW.adjoint_stable_filtration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:43:09.721797+00:00
-- url     : https://prove2.me/submissions/29586fed-7fa4-46bc-aa17-6b4ac6ded4a1

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CasimirPowerCommute
import Theorems.Thm_PositivityTheory_CW_AdjointWordFiltration_U_mono
import Theorems.Thm_PositivityTheory_CW_AdjointWordFiltration_word_adj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
namespace PositivityTheory.CW
theorem _root_.solution : FiltrationAdjointStable := by
  intro n ε V _ _ E hM k u hu
  unfold U at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨u', hu', h⟩ := AdjointWordFiltration.word_adj ε E hM.uni l
    exact ⟨u', AdjointWordFiltration.U_mono E hl hu', h⟩
  | zero => exact ⟨0, Submodule.zero_mem _, fun x y => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', hx⟩ := hx
    obtain ⟨y', hy', hy⟩ := hy
    exact ⟨x' + y', Submodule.add_mem _ hx' hy', fun a b => by
      simp only [LinearMap.add_apply, inner_add_left, inner_add_right, hx, hy]⟩
  | smul c x _ hx =>
    obtain ⟨x', hx', hx⟩ := hx
    refine ⟨starRingEnd ℂ c • x', Submodule.smul_mem _ _ hx', fun a b => ?_⟩
    rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_conj, hx]
end PositivityTheory.CW
