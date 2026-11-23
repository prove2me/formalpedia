-- Prove2me | solution 1 for PI.AprimeInfA.orb_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:56.554011+00:00
-- url     : https://prove2.me/submissions/5dc8d29e-f66d-4237-bbbc-adaa9a40264e

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
variable {X : Type} [MulAction G X] [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]
namespace PI.AprimeInfA
theorem _root_.solution (x0 : X) (g : G) :
    ((g : G ⧸ MulAction.stabilizer G x0)).out • x0 = g • x0 := by

  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (MulAction.stabilizer G x0) g
  rw [hk, mul_smul, MulAction.mem_stabilizer_iff.mp k.2]
end PI.AprimeInfA
