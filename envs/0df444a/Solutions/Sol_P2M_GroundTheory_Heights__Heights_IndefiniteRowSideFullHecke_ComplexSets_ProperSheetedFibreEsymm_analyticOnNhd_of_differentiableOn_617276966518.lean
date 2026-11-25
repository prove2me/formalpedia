-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_analyticOnNhd_of_differentiableOn_617276966518
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:31:58.708275+00:00
-- url     : https://prove2.me/submissions/60094be4-b8fe-4565-a9a8-dc3259ada104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperSheetedFibreEsymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperSheetedFibreEsymm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Set Complex
open scoped Real
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperSheetedFibreEsymm
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperSheetedFibreEsymm
theorem _root_.solution (hcirc : ParametricCircleIntegralAnalytic.Statement) {k : ℕ}
    {U : Set (Fin k → ℂ)} {F : (Fin k → ℂ) → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ F U := by
  have h := hcirc (Fin k) (fun p => F p.1 * p.2⁻¹) (U ×ˢ {s | s ≠ 0}) U 0 1 zero_le_one
    (hU.prod isOpen_ne) hU
    ((hF.comp differentiable_fst.differentiableOn fun p hp => hp.1).mul
      (differentiable_snd.differentiableOn.inv fun p hp => hp.2))
    (fun x hx s hs => ⟨hx, by rintro rfl; simp at hs⟩)
  have hinv : (∮ z in C(0, 1), z⁻¹) = 2 * π * I := by
    simpa using circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (w := 0) (R := 1) (by simp)
  intro x hx
  refine ((h x hx).mul (analyticAt_const (v := (2 * π * I)⁻¹))).congr (Eventually.of_forall fun y => ?_)
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  simp only [Pi.mul_apply, circleIntegral.integral_const_mul, hinv]
  field_simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperSheetedFibreEsymm
