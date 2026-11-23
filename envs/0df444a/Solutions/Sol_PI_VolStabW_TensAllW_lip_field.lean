-- Prove2me | solution 1 for PI.VolStabW.TensAllW.lip_field
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:34.395694+00:00
-- url     : https://prove2.me/submissions/787e5885-8437-4a7d-8759-789b729a1fc2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.TensAllW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice Matrix
namespace PI.VolStabW.TensAllW
theorem _root_.solution (K : Type) [Field K] : LIP K := by
  intro m n _ _ _ _ W hW
  have hk : LinearMap.ker (Matrix.toLin' W) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    exact hW c (by simpa [Matrix.toLin'_apply] using hc)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' W) hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 : Matrix.toLin' (LinearMap.toMatrix' g * W) = LinearMap.id := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', hg]
  have h2 := congrArg LinearMap.toMatrix' h1
  rwa [LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h2
end PI.VolStabW.TensAllW
