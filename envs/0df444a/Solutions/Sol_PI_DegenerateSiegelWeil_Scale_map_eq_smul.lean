-- Prove2me | solution 1 for PI.DegenerateSiegelWeil.Scale.map_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:33.133289+00:00
-- url     : https://prove2.me/submissions/1419d53a-c878-493e-8afd-4b16afac3092

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_MulTupApplyEqSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DegenerateSiegelWeil PI.DegenerateSiegelWeil.Scale
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW PI.VolStabSW.TensAllW
open scoped ENNReal NNReal TensorProduct Matrix
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
namespace PI.DegenerateSiegelWeil.Scale
theorem _root_.solution (μ : Measure G) [μ.IsAddHaarMeasure] (e : G ≃ₜ+ G) :
    μ.map e = (((addEquivAddHaarChar e)⁻¹ : ℝ≥0) : ℝ≥0∞) • μ := by
  have h := MeasureTheory.addEquivAddHaarChar_smul_map μ e
  have hc : (addEquivAddHaarChar e : ℝ≥0) ≠ 0 := (MeasureTheory.addEquivAddHaarChar_pos e).ne'
  conv_rhs => rw [← h]
  rw [ENNReal.smul_def (addEquivAddHaarChar e), smul_smul, ← ENNReal.coe_mul, inv_mul_cancel₀ hc,
    ENNReal.coe_one, one_smul]
end PI.DegenerateSiegelWeil.Scale
