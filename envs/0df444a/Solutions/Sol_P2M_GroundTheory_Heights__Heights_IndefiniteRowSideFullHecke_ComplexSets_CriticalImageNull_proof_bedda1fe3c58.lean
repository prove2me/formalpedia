-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CriticalImageNull_proof_bedda1fe3c58
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:13:47.654812+00:00
-- url     : https://prove2.me/submissions/e846a014-4975-4b8a-b3e4-cc3f0b063b45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hausdorffMeasure_image_eq_zero_of_not_injective_0e64433aadc0

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
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace CriticalImageNull
theorem _root_.solution : CriticalImageNull.Statement := by
  intro d n U f hU hf
  let b := Pi.basis (fun _ : Fin d => Complex.basisOneI)
  let e : ((Σ _ : Fin d, Fin 2) → ℝ) ≃L[ℝ] (Fin d → ℂ) :=
    b.equivFun.symm.toContinuousLinearEquiv
  have hcard : Fintype.card (Σ _ : Fin d, Fin 2) = 2 * d := by
    simp [Fintype.card_sigma, mul_comm]
  set C := {s | s ∈ U ∧ ¬ Function.Injective (fderiv ℂ f s)} with hC
  have himg : f '' C = (f ∘ e) '' (e ⁻¹' C) := by
    rw [image_comp, image_preimage_eq _ e.surjective]
  have key := hausdorffMeasure_image_eq_zero_of_not_injective (f := f ∘ e) (s := e ⁻¹' C)
    (f' := fun x => ((fderiv ℂ f (e x)).restrictScalars ℝ).comp (e : _ →L[ℝ] _)) ?_ ?_
  · rw [himg, ← hcard]
    exact key
  · intro x hx
    have hU' : U ∈ 𝓝 (e x) := hU.mem_nhds hx.1
    have h1 : HasFDerivAt f (fderiv ℂ f (e x)) (e x) := (hf.differentiableAt hU').hasFDerivAt
    exact ((h1.restrictScalars ℝ).comp x e.hasFDerivAt).hasFDerivWithinAt
  · intro x hx hinj
    apply hx.2
    intro a c hac
    have h2 := @hinj (e.symm a) (e.symm c) (by simpa using hac)
    simpa using congrArg e h2
end CriticalImageNull
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
