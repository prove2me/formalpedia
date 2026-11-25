-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.symm_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:55:53.718822+00:00
-- url     : https://prove2.me/submissions/6284f325-a293-4dc3-acc0-4e9bd9e46401

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCCalc
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_iter_diffAt
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_predPerm_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Set Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) {k : ℕ}
    (ih : ∀ c ∈ Ω, ∀ (v : Fin k → V) (σ : Equiv.Perm (Fin k)), iteratedFDeriv ℂ k F c (v ∘ σ) = iteratedFDeriv ℂ k F c v)
    {c : V} (hc : c ∈ Ω) (σ : Equiv.Perm (Fin (k + 1))) (h0 : σ 0 = 0) (v : Fin (k + 1) → V) :
    iteratedFDeriv ℂ (k + 1) F c (v ∘ σ) = iteratedFDeriv ℂ (k + 1) F c v := by
  have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k F) c := iter_diffAt hΩ hF k hc
  have ht : Fin.tail (v ∘ σ) = Fin.tail v ∘ predPerm σ h0 := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    rw [predPerm_succ]
  have h0' : (v ∘ σ) 0 = v 0 := by simp [h0]
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left, ht, h0',
    ← fderiv_continuousMultilinear_apply_const_apply hd,
    ← fderiv_continuousMultilinear_apply_const_apply hd]
  congr 1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hΩ.mem_nhds hc] with y hy
  exact ih y hy (Fin.tail v) (predPerm σ h0)
end PositivityTheory.Rg.Sw.LVs.TC
