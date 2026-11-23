-- Prove2me | solution 1 for PositivityTheory.RgBcC.LfSt.ChainPf.Cact.pd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:28.285348+00:00
-- url     : https://prove2.me/submissions/2948c605-2664-49d5-842b-18d24c8d3448

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ArchimedeanGelfandKernels_LeftEquivariantFunctions_GLMatrixDerivatives_ChainOfCactA
import Theorems.Thm_PositivityTheory_RgBcC_LfSt_ChainPf_Cact_hasFDerivAt_pd

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
theorem _root_.solution {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) {U : Set H} (hU : IsOpen U)
    (hUO : U ⊆ O) {z : Z} (hz : z ∈ OZ) (h0 : ∀ x ∈ U, Φ (x, z) = 0) {x : H} (hx : x ∈ U) : pd Φ (x, z) = 0 := by
  have h1 := hasFDerivAt_pd hO hOZ hΦ (hUO hx) hz
  have h2 : HasFDerivAt (fun x' => Φ (x', z)) (0 : H →L[ℝ] W) x :=
    (hasFDerivAt_const (0 : W) x).congr_of_eventuallyEq
      (eventually_of_mem (hU.mem_nhds hx) fun x' hx' => h0 x' hx')
  exact h1.unique h2
end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
