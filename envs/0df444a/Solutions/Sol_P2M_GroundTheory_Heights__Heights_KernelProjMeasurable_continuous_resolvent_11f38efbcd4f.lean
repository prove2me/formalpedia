-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_continuous_resolvent_11f38efbcd4f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:25:54.160844+00:00
-- url     : https://prove2.me/submissions/bbd810aa-6935-4933-93a9-91983aee67f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PKernelProjMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_isUnit_shifted_49b303e062a1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology ContinuousLinearMap
noncomputable section
open GroundTheory.Heights₂.Heights.KernelProjMeasurable
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
namespace GroundTheory.Heights₂.Heights.KernelProjMeasurable
theorem _root_.solution {X : Type*} [TopologicalSpace X] {A : X → E →L[ℂ] F} (hA : Continuous A) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun x => resolvent (A x) ε := by
  have hadj : Continuous fun x => ContinuousLinearMap.adjoint (A x) :=
    ContinuousLinearMap.adjoint.continuous.comp hA
  have hT : Continuous fun x => shifted (A x) ε := by
    simp only [shifted]
    exact (hadj.clm_comp hA).add continuous_const
  have hI : Continuous fun x => Ring.inverse (shifted (A x) ε) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    have h := NormedRing.inverse_continuousAt (isUnit_shifted (A x) hε).unit
    rw [IsUnit.unit_spec] at h
    exact ContinuousAt.comp (g := Ring.inverse) (f := fun x => shifted (A x) ε) h hT.continuousAt
  show Continuous fun x => (ε : ℂ) • Ring.inverse (shifted (A x) ε)
  exact hI.const_smul (ε : ℂ)
end GroundTheory.Heights₂.Heights.KernelProjMeasurable
