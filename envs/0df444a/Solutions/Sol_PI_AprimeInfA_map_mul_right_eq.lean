-- Prove2me | solution 1 for PI.AprimeInfA.map_mul_right_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:22.798228+00:00
-- url     : https://prove2.me/submissions/f1a90a2d-12c6-4485-af14-b9ca90a02337

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfA
open MeasureTheory Topology TopologicalSpace Set
open scoped ENNReal NNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.AprimeInfA
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] (g : G) :
    μ.map (· * g) = Measure.modularCharacterFun g • μ := by

  rw [MeasureTheory.Measure.modularCharacterFun_eq_haarScalarFactor μ g]
  exact Measure.isMulLeftInvariant_eq_smul _ μ
end PI.AprimeInfA
