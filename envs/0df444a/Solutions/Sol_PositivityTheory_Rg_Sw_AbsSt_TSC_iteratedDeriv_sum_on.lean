-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.AbsSt.TSC.iteratedDeriv_sum_on
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:28.338016+00:00
-- url     : https://prove2.me/submissions/882bf021-2bd9-456b-9d8a-f9cb050b2fde

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AbsoluteConvergence_IteratedDerivSumOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.TSC
namespace PositivityTheory.Rg.Sw.AbsSt.TSC
theorem _root_.solution {ι : Type} (s : Finset ι) {U : Set ℂ} (hU : IsOpen U) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) U) (r : ℕ) :
    (∀ i ∈ s, DifferentiableOn ℂ (iteratedDeriv r (f i)) U) ∧
    EqOn (iteratedDeriv r (fun w => ∑ i ∈ s, f i w)) (fun w => ∑ i ∈ s, iteratedDeriv r (f i) w) U := by
  induction r with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact ⟨hf, fun _ _ => rfl⟩
  | succ r ih =>
    obtain ⟨hd, he⟩ := ih
    refine ⟨fun i hi => ?_, fun z hz => ?_⟩
    · rw [iteratedDeriv_succ]
      exact (hd i hi).deriv hU
    · simp only [iteratedDeriv_succ]
      have hev : iteratedDeriv r (fun w => ∑ i ∈ s, f i w) =ᶠ[𝓝 z]
          (fun w => ∑ i ∈ s, iteratedDeriv r (f i) w) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hz) he
      rw [hev.deriv_eq]
      first
        | exact deriv_fun_sum (fun i hi => (hd i hi).differentiableAt (hU.mem_nhds hz))
        | exact deriv_sum (fun i hi => (hd i hi).differentiableAt (hU.mem_nhds hz))
end PositivityTheory.Rg.Sw.AbsSt.TSC
