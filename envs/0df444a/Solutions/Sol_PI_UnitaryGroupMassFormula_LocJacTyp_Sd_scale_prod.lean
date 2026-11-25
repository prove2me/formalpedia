-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.Sd.scale_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:30:53.169242+00:00
-- url     : https://prove2.me/submissions/0cc57ec3-cf91-456a-b4ee-d1b11b5e0c44

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_DiagonalPhaseFirstVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_IsCompactDbox
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_haar_smul_map
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type} [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd
theorem _root_.solution (μ0 : Measure V) [μ0.IsAddHaarMeasure] (c : Fv F v) (hc : c ≠ 0)
    (A B : Set V) (hA : MeasurableSet A) (hB : MeasurableSet B) (hA0 : μ0 A ≠ 0) (hAt : μ0 A ≠ ⊤) :
    μ0 ((fun x : V => c • x) ⁻¹' A) * μ0 ((fun x : V => c⁻¹ • x) ⁻¹' B) = μ0 A * μ0 B := by
  have := haar_smul_map v μ0 c hc
  have := haar_smul_map v μ0 c⁻¹ (inv_ne_zero hc)
  have hm : Measurable fun x : V => c • x := (continuous_const_smul c).measurable
  have hm' : Measurable fun x : V => c⁻¹ • x := (continuous_const_smul c⁻¹).measurable
  obtain ⟨s1, e1⟩ : ∃ s : NNReal, Measure.map (fun x : V => c • x) μ0 = s • μ0 :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ μ0⟩
  obtain ⟨s2, e2⟩ : ∃ s : NNReal, Measure.map (fun x : V => c⁻¹ • x) μ0 = s • μ0 :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ μ0⟩
  have hcomp : Measure.map (fun x : V => c⁻¹ • x) (Measure.map (fun x : V => c • x) μ0) = μ0 := by
    rw [Measure.map_map hm' hm]
    have : ((fun x : V => c⁻¹ • x) ∘ fun x : V => c • x) = id := by
      funext x; simp [smul_smul, inv_mul_cancel₀ hc]
    rw [this, Measure.map_id]
  have hss : ((s1 : ENNReal) * s2) * μ0 A = 1 * μ0 A := by
    have h := congrArg (fun m : Measure V => m A) hcomp
    rw [e1, Measure.map_smul, e2, smul_smul] at h
    rw [one_mul]
    conv_rhs => rw [← h]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul]
  have hs : (s1 : ENNReal) * s2 = 1 := (ENNReal.mul_left_inj hA0 hAt).1 hss
  rw [← Measure.map_apply hm hA, ← Measure.map_apply hm' hB, e1, e2]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  calc (s1 : ENNReal) * μ0 A * (s2 * μ0 B) = ((s1 : ENNReal) * s2) * (μ0 A * μ0 B) := by ring
    _ = μ0 A * μ0 B := by rw [hs, one_mul]
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
