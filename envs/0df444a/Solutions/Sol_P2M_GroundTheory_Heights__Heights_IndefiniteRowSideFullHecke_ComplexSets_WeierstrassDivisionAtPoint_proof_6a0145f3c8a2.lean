-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassDivisionAtPoint_proof_6a0145f3c8a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:59:48.618825+00:00
-- url     : https://prove2.me/submissions/2ca914cc-36d0-4317-beb4-c127da75750b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassDivisionAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeierstrassDivisionAtPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coordinateToLast_none_64aa5068a5d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coordinateToLast_some_dae1a9143cd1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lastToCoordinate_coordinateToLast_6599e7c66a76
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lastToCoordinate_pointWithLast_328d2480d2e5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_zeroCoordinate_apply_d48952ae67a2


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
open Topology Filter
noncomputable section
variable {τ : Type} [DecidableEq τ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace WeierstrassDivisionAtPoint
theorem _root_.solution (hW : WeierstrassDivision.Statement) :
    WeierstrassDivisionAtPoint.Statement := by
  intro τ _ _ y₀ c d F g hF hg hord
  have hA : ∀ h : (τ → ℂ) → ℂ, AnalyticAt ℂ h y₀ →
      AnalyticAt ℂ (fun w => h (y₀ + lastToCoordinate c w)) 0 := by
    intro h hh
    exact AnalyticAt.fun_comp_of_eq hh (analyticAt_const.add ((lastToCoordinate c).analyticAt 0)) (by simp)
  have hord' : analyticOrderAt
      (fun t => (fun w => F (y₀ + lastToCoordinate c w)) (pointWithLast 0 t)) 0 = d := by
    simpa only [lastToCoordinate_pointWithLast] using hord
  obtain ⟨q, a, hq, ha, heq⟩ := hW {c' // c' ≠ c} d _ _ (hA F hF) (hA g hg) hord'
  refine ⟨fun y => q (coordinateToLast c (y - y₀)), fun j u => a j (fun c' => u c'.1 - y₀ c'.1), ?_, ?_, ?_⟩
  · exact AnalyticAt.fun_comp_of_eq hq
      (((coordinateToLast c).analyticAt _).comp (analyticAt_id.sub analyticAt_const)) (by simp)
  · intro j
    have hR : AnalyticAt ℂ (fun u : τ → ℂ => fun c' : {c' // c' ≠ c} => u c'.1 - y₀ c'.1) (zeroCoordinate c y₀) := by
      have hL := ((ContinuousLinearMap.pi fun c' : {c' // c' ≠ c} =>
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) c'.1).analyticAt (zeroCoordinate c y₀)).sub
          (analyticAt_const (v := fun c' : {c' // c' ≠ c} => y₀ c'.1))
      convert hL using 1
      funext u c'
      rfl
    refine AnalyticAt.fun_comp_of_eq (ha j) hR ?_
    funext c'
    simp [zeroCoordinate_apply, c'.2]
  · have hT : Tendsto (fun y => coordinateToLast c (y - y₀)) (𝓝 y₀) (𝓝 0) := by
      have hc : Continuous fun y : τ → ℂ => coordinateToLast c (y - y₀) :=
        (coordinateToLast c).continuous.comp (continuous_id.sub continuous_const)
      simpa using hc.tendsto y₀
    filter_upwards [hT.eventually heq] with y hy
    have hy' : y₀ + lastToCoordinate c (coordinateToLast c (y - y₀)) = y := by
      rw [lastToCoordinate_coordinateToLast]; abel
    simp only [hy'] at hy
    rw [hy]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (fun i : {c' // c' ≠ c} => coordinateToLast c (y - y₀) (some i)) =
        fun c' => zeroCoordinate c y c'.1 - y₀ c'.1 := by
      funext c'
      rw [coordinateToLast_some, zeroCoordinate_apply, if_neg c'.2, Pi.sub_apply]
    rw [h1, coordinateToLast_none, Pi.sub_apply]
end WeierstrassDivisionAtPoint
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
