-- Prove2me | solution 1 for PI.VolStabSW.orb_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:03.040871+00:00
-- url     : https://prove2.me/submissions/d600ae46-eca2-4a7d-b592-4a87e586eea2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WeilQuotMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExStabSt
import Theorems.Thm_PI_VolStabSW_orb_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal
variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G X] [TopologicalSpace X] [MeasurableSpace X]
namespace PI.VolStabSW
theorem _root_.solution (x0 : X) (g : G) (q : G ⧸ MulAction.stabilizer G x0) :
    (g • q).out • x0 = g • (q.out • x0) := by
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  have : g • ((q.out : G) : G ⧸ MulAction.stabilizer G x0) =
      ((g * q.out : G) : G ⧸ MulAction.stabilizer G x0) := rfl
  rw [this, orb_mk, mul_smul]
end PI.VolStabSW
