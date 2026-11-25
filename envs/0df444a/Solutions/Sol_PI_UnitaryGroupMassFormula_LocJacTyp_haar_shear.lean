-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.haar_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:59:42.079491+00:00
-- url     : https://prove2.me/submissions/2582b834-4067-4022-95bd-84cf905731a6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitShear
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_locallyCompact_Fv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_secondCountable_Fv
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim
variable {W : Type} [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [LocallyCompactSpace W] [SecondCountableTopology W] [T2Space W] [MeasurableSpace W] [BorelSpace W]
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (μ : Measure W) [μ.IsAddHaarMeasure] (Φ : W ≃ₜ+ W) (K : Set W)
    (hK : IsCompact K) (hKo : IsOpen K) (hK0 : K.Nonempty) (hΦ : Φ ⁻¹' K = K) (S : Set W) :
    μ (Φ ⁻¹' S) = μ S := by
  have hmap : ∀ T, (μ.map Φ) T = μ (Φ ⁻¹' T) := fun T =>
    (Φ.toHomeomorph.toMeasurableEquiv).map_apply (μ := μ) T
  have e := Measure.isAddLeftInvariant_eq_smul (μ.map Φ) μ
  have hpos : μ K ≠ 0 := hKo.measure_ne_zero μ hK0
  have hfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have h1 := congrArg (fun ν : Measure W => ν K) e
  simp only [hmap, hΦ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
  have hc : ((Measure.addHaarScalarFactor (μ.map Φ) μ : NNReal) : ENNReal) = 1 := by
    have h2 : (1 : ENNReal) * μ K = (Measure.addHaarScalarFactor (μ.map Φ) μ : ENNReal) * μ K := by
      rw [one_mul]; exact h1
    exact ((ENNReal.mul_left_inj hpos hfin).1 h2).symm
  rw [← hmap, e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hc, one_mul]
end PI.UnitaryGroupMassFormula.LocJacTyp
