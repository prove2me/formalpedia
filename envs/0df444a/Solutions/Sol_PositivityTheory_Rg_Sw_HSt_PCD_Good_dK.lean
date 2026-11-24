-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.PCD.Good.dK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:39.015206+00:00
-- url     : https://prove2.me/submissions/15bb1804-8857-4b43-9008-0abed15750c7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD

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
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.PCD
variable {F X : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X] [SecondCountableTopology X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set F} {K : F → X → E}
namespace PositivityTheory.Rg.Sw.HSt.PCD
namespace Good
theorem _root_.solution (hΩ : IsOpen Ω) (hK : Good Ω K) : Good Ω (fun x u => fderiv ℝ (K · u) x) := by
  refine ⟨fun u => ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 (hK.smooth u)).2, fun N => ?_, fun x hx => ?_⟩
  · have h : ContinuousOn (fun p : F × X => (continuousMultilinearCurryRightEquiv' ℝ N F E)
        (iteratedFDeriv ℝ (N + 1) (K · p.2) p.1)) (Ω ×ˢ univ) :=
      (LinearIsometryEquiv.continuous _).comp_continuousOn (hK.cont (N + 1))
    refine h.congr fun p _ => ?_
    simp only [Function.comp_apply]
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp
  · obtain ⟨V, hV, hxV, C, hC, hKV⟩ := hK.supp x hx
    refine ⟨V, hV, hxV, C, hC, fun x' hx' u hu => ?_⟩
    have : (K · u) =ᶠ[𝓝 x'] fun _ => 0 := by
      filter_upwards [hV.mem_nhds hx'] with y hy using hKV y hy u hu
    rw [this.fderiv_eq]
    simp
end Good
end PositivityTheory.Rg.Sw.HSt.PCD
