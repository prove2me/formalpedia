-- Prove2me | solution 1 for PositivityTheory.RgBcC.LfSt.ChainPf.Cact.locSupp_pd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:15.805832+00:00
-- url     : https://prove2.me/submissions/a23626df-1f60-40ec-9f81-60293e650987

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ArchimedeanGelfandKernels_LeftEquivariantFunctions_GLMatrixDerivatives_ChainOfCactA
import Theorems.Thm_PositivityTheory_RgBcC_LfSt_ChainPf_Cact_pd_eq_zero

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
namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cact
theorem _root_.solution {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W} {ι : Γ → Z}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hι : ∀ y, ι y ∈ OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ))
    (hS : LocSupp O ι Φ) : LocSupp O ι (pd Φ) := by
  intro x₀ hx₀
  obtain ⟨U, hUo, hxU, hUO, K, hK, hKz⟩ := hS x₀ hx₀
  exact ⟨U, hUo, hxU, hUO, K, hK, fun x hx y hy =>
    pd_eq_zero hO hOZ hΦ hUo hUO (hι y) (fun x' hx' => hKz x' hx' y hy) hx⟩
end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
