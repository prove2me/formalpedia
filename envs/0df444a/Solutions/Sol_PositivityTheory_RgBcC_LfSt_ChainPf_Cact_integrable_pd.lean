-- Prove2me | solution 1 for PositivityTheory.RgBcC.LfSt.ChainPf.Cact.integrable_pd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:24.239884+00:00
-- url     : https://prove2.me/submissions/eba42755-22ed-4f5e-a527-bde86724917f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ArchimedeanGelfandKernels_LeftEquivariantFunctions_GLMatrixDerivatives_ChainOfCactA
import Theorems.Thm_PositivityTheory_RgBcC_LfSt_ChainPf_Cact_contDiffOn_pd
import Theorems.Thm_PositivityTheory_RgBcC_LfSt_ChainPf_Cact_locSupp_pd
import Theorems.Thm_PositivityTheory_RgBcC_LfSt_ChainPf_Cact_integrable_slice

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
theorem _root_.solution {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W} (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ)
    (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) (hS : LocSupp O ι Φ) {x : H} (hx : x ∈ O) :
    Integrable (fun y : Γ => pd Φ (x, ι y)) μ := by
  obtain ⟨U, hUo, hxU, hUO, K, hK, hKz⟩ := locSupp_pd hO hOZ hι hΦ hS x hx
  exact integrable_slice μ hιc hι (contDiffOn_pd hO hOZ hΦ).continuousOn hx hK fun y hy => hKz x hxU y hy
end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
