-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.phi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:49:11.375746+00:00
-- url     : https://prove2.me/submissions/a2349cdb-359f-40e9-a4e1-9ec01bda04d8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAFTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_MapPhiOfModM
import Theorems.Thm_PI_VolSemiDirect_W_Cj_phi_apply

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
open MeasureTheory Measure
open scoped NNReal
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution (X Y : GL (Fin k) A) : phi (X * Y) = (phi Y).trans (phi X) := by
  apply ContinuousAddEquiv.ext
  intro v
  simp only [ContinuousAddEquiv.trans_apply, phi_apply, Units.val_mul, Matrix.mulVec_mulVec]
end PI.VolSemiDirect.W.Cj
