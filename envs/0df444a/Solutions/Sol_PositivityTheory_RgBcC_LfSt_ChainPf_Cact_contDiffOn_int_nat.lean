-- Prove2me | solution 1 for PositivityTheory.RgBcC.LfSt.ChainPf.Cact.contDiffOn_int_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:20.873806+00:00
-- url     : https://prove2.me/submissions/af298bc8-d1c5-43ed-8841-a543869ec460

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ArchimedeanGelfandKernels_LeftEquivariantFunctions_GLMatrixDerivatives_ChainOfCactA
import Theorems.Thm_PositivityTheory_RgBcC_LfSt_ChainPf_Cact_contDiffOn_pd
import Theorems.Thm_PositivityTheory_RgBcC_LfSt_ChainPf_Cact_locSupp_pd
import Theorems.Thm_PositivityTheory_RgBcC_LfSt_ChainPf_Cact_hasFDerivAt_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Set
open scoped ContDiff
open PositivityTheory PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Cact
variable {H Z : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {Γ : Type} [TopologicalSpace Γ] [T2Space Γ] [MeasurableSpace Γ] [BorelSpace Γ]
variable {O : Set H} {OZ : Set Z}
variable (μ : Measure Γ) [IsFiniteMeasureOnCompacts μ] {ι : Γ → Z}
namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cact
theorem _root_.solution (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ) :
    ∀ (m : ℕ) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W}, ContDiffOn ℝ ∞ Φ (O ×ˢ OZ) → LocSupp O ι Φ →
    ContDiffOn ℝ m (fun x => ∫ y : Γ, Φ (x, ι y) ∂μ) O := by
  intro m
  induction m with
  | zero =>
    intro W _ _ _ Φ hΦ hS
    refine contDiffOn_zero.2 fun x hx => ?_
    exact (hasFDerivAt_int μ hO hOZ hιc hι hΦ hS hx).continuousAt.continuousWithinAt
  | succ m ih =>
    intro W _ _ _ Φ hΦ hS
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hO]
    refine ⟨fun x hx => (hasFDerivAt_int μ hO hOZ hιc hι hΦ hS hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have h1 := ih (contDiffOn_pd hO hOZ hΦ) (locSupp_pd hO hOZ hι hΦ hS)
    exact h1.congr fun x hx => (hasFDerivAt_int μ hO hOZ hιc hι hΦ hS hx).fderiv
end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
