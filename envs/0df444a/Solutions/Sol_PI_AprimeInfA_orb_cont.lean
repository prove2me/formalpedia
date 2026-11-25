-- Prove2me | solution 1 for PI.AprimeInfA.orb_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:53.353749+00:00
-- url     : https://prove2.me/submissions/611790e5-1073-4cbb-bc92-dc6485181e33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Theorems.Thm_PI_AprimeInfA_orb_mk

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
theorem _root_.solution (x0 : X) (hc : Continuous fun g : G => g • x0) :
    Continuous (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) := by

  have e : (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) ∘ QuotientGroup.mk =
      fun g : G => g • x0 := by
    funext g
    exact orb_mk x0 g
  exact (QuotientGroup.isQuotientMap_mk (MulAction.stabilizer G x0)).continuous_iff.2 (by rw [e]; exact hc)
end PI.AprimeInfA
