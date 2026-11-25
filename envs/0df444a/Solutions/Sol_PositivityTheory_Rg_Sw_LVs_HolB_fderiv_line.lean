-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.HolB.fderiv_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:47:00.796648+00:00
-- url     : https://prove2.me/submissions/4789e9d8-d108-4f3b-828f-7a1e978c050d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_HermRealSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Filter Topology Set Metric Matrix
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs.HolB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
private theorem fderiv_apply_eq_zero_of_const_on_real_line {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {f : E → W} {y v : E}
    (hf : DifferentiableAt ℂ f y) (h : ∀ t : ℝ, f (y + (t : ℂ) • v) = f y) : fderiv ℂ f y v = 0 := by
  have hl : HasDerivAt (fun t : ℝ => y + (t : ℂ) • v) v 0 := by
    have h0 := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).smul_const v).const_add y
    convert h0 using 1
    · rfl
    · rw [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]
  have h1 : HasFDerivAt f ((fderiv ℂ f y).restrictScalars ℝ) (y + ((0 : ℝ) : ℂ) • v) := by
    simpa using hf.hasFDerivAt.restrictScalars ℝ
  have hc := h1.comp_hasDerivAt (0 : ℝ) hl
  have hk : (f ∘ fun t : ℝ => y + (t : ℂ) • v) = fun _ => f y := funext h
  rw [hk] at hc
  exact ((hasDerivAt_const (0 : ℝ) (f y)).unique hc).symm
end PositivityTheory.Rg.Sw.LVs.HolB
end
end

set_option autoImplicit false
noncomputable section
open Filter Topology Set Metric Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.HolB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.HolB
theorem _root_.solution {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {f : M2 n → W} {y v : M2 n}
    (hf : DifferentiableAt ℂ f y) (h : ∀ t : ℝ, f (y + (t : ℂ) • v) = f y) : fderiv ℂ f y v = 0 := by
  exact fderiv_apply_eq_zero_of_const_on_real_line hf h
end PositivityTheory.Rg.Sw.LVs.HolB
