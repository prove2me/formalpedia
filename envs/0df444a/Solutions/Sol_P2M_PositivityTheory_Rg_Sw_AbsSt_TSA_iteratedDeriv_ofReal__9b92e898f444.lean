-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_AbsSt_TSA_iteratedDeriv_ofReal__9b92e898f444
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:58.899489+00:00
-- url     : https://prove2.me/submissions/1425301d-78b5-4586-99f8-42954fc2443b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AbsoluteConvergence_IteratedDerivOfReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.TSA
namespace PositivityTheory.Rg.Sw.AbsSt.TSA
theorem _root_.solution {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    {h : ℝ → ℂ} (hmem : ∀ x : ℝ, (x : ℂ) ∈ U) (hFh : ∀ x : ℝ, F x = h x) (p : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv p F) U ∧ ∀ x : ℝ, iteratedDeriv p F x = iteratedDeriv p h x := by
  induction p with
  | zero => simpa using ⟨hF, hFh⟩
  | succ p ih =>
    obtain ⟨hd, he⟩ := ih
    refine ⟨?_, fun x => ?_⟩
    · rw [iteratedDeriv_succ]
      exact hd.deriv hU
    · rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have h0 : HasDerivAt (iteratedDeriv p F) (deriv (iteratedDeriv p F) x) (x : ℂ) :=
        (hd.differentiableAt (hU.mem_nhds (hmem x))).hasDerivAt
      have h3 : HasDerivAt (fun y : ℝ => iteratedDeriv p F y) (deriv (iteratedDeriv p F) x) x := h0.comp_ofReal
      have h4 : (fun y : ℝ => iteratedDeriv p F y) = iteratedDeriv p h := funext he
      rw [h4] at h3
      exact h3.deriv.symm
end PositivityTheory.Rg.Sw.AbsSt.TSA
