-- Prove2me | solution 1 for PI.AprimeInfA.orb_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:56.492991+00:00
-- url     : https://prove2.me/submissions/4184b579-cbfe-4971-8930-7219fdce01e1

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
theorem _root_.solution (x0 : X) :
    Function.Injective (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) := by

  intro q q' h
  simp only at h
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
    MulAction.mem_stabilizer_iff, mul_smul, ← h, ← mul_smul, inv_mul_cancel, one_smul]
end PI.AprimeInfA
