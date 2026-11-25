-- Prove2me | solution 1 for PI.WSF.unitary_haar_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:36:18.574056+00:00
-- url     : https://prove2.me/submissions/279a7f93-fd0b-4c90-8645-09e77b880c9c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_ConstructionB
import Theorems.Thm_PI_WSF_isMulRightInvariant_of_compact
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WSF
open Formalism.BasicNotions MvPolynomial MeasureTheory Measure TopologicalSpace Matrix
namespace PI.WSF
theorem _root_.solution : HaarU := by
  intro N
  haveI : CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) := compactSpace_unitaryGroup N
  let μG : Measure (Matrix.unitaryGroup (Fin N) ℂ) := Measure.haarMeasure ⊤
  haveI : μG.IsMulRightInvariant := isMulRightInvariant_of_compact μG
  have hm : Measurable (Subtype.val : Matrix.unitaryGroup (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ) :=
    measurable_subtype_coe
  refine ⟨Measure.map Subtype.val μG, ?_, ?_, ?_, ?_⟩
  · constructor
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ]
    have h1 := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup (Fin N) ℂ)))
    simpa using h1
  · have hmeas : MeasurableSet {x : Matrix (Fin N) (Fin N) ℂ | x ∈ Matrix.unitaryGroup (Fin N) ℂ} :=
      (isCompact_unitaryGroup N).isClosed.measurableSet
    rw [ae_map_iff hm.aemeasurable hmeas]
    exact Filter.Eventually.of_forall fun y => y.2
  · intro u hu f hf
    have hs : AEStronglyMeasurable (fun x => f (x * u)) (Measure.map Subtype.val μG) :=
      (hf.comp (continuous_mul_right u)).aestronglyMeasurable
    rw [integral_map hm.aemeasurable hs, integral_map hm.aemeasurable hf.aestronglyMeasurable]
    have h1 := integral_mul_right_eq_self (μ := μG)
      (fun y : Matrix.unitaryGroup (Fin N) ℂ => f (y : Matrix (Fin N) (Fin N) ℂ)) ⟨u, hu⟩
    simpa using h1
  · intro u hu f hf
    have hs : AEStronglyMeasurable (fun x => f (u * x)) (Measure.map Subtype.val μG) :=
      (hf.comp (continuous_mul_left u)).aestronglyMeasurable
    rw [integral_map hm.aemeasurable hs, integral_map hm.aemeasurable hf.aestronglyMeasurable]
    have h1 := integral_mul_left_eq_self (μ := μG)
      (fun y : Matrix.unitaryGroup (Fin N) ℂ => f (y : Matrix (Fin N) (Fin N) ℂ)) ⟨u, hu⟩
    simpa using h1
end PI.WSF
