-- Prove2me | solution 1 for PI.InvTopW.thetaV_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:15:23.47451+00:00
-- url     : https://prove2.me/submissions/3aa638dd-46e4-4092-86a8-3acc2ef10055

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LinearIndependentOneBeta
import Theorems.Thm_PI_InvTopW_sum_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
variable (I : AutInst)
namespace PI.InvTopW
theorem _root_.solution (v : InfinitePlace I.F) (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    thetaV I v t = ∑ k, evV I v (coord I k t) * I.φ v (basisE I k) := by
  conv_lhs => rw [← sum_coord I t]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl
end PI.InvTopW
