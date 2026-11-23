-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.trG_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:17.782891+00:00
-- url     : https://prove2.me/submissions/24fd627d-8bbb-4aa1-8dc7-1a5d6404ec72

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_MapPhiOfModM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_NnrealEqOneOfMulSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Measure
open scoped NNReal
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution (X : GL (Fin k) A) :
    ((trG X : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) = (X : Matrix (Fin k) (Fin k) A).transpose :=
  rfl
end PI.VolSemiDirect.W.Cj
