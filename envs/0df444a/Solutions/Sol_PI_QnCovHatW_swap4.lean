-- Prove2me | solution 1 for PI.QnCovHatW.swap4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:07:51.533538+00:00
-- url     : https://prove2.me/submissions/db1d6b69-fe21-4476-9f75-2f0298a5c3e0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_InjDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_SkipOneEqSuccAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix Formalism.REAL Formalism.FourierDecayAlt.Q
open PI PI.QnCovHatW
namespace PI.QnCovHatW
theorem _root_.solution {M : Type*} [AddCommMonoid M] {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → M) :
    ∑ i, ∑ j, ∑ i', ∑ j', f i j i' j' = ∑ i', ∑ j', ∑ i, ∑ j, f i j i' j' := by
  calc ∑ i, ∑ j, ∑ i', ∑ j', f i j i' j' = ∑ i, ∑ i', ∑ j', ∑ j, f i j i' j' := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i' _ => Finset.sum_comm
    _ = ∑ i', ∑ i, ∑ j', ∑ j, f i j i' j' := Finset.sum_comm
    _ = ∑ i', ∑ j', ∑ i, ∑ j, f i j i' j' :=
        Finset.sum_congr rfl fun i' _ => Finset.sum_comm
end PI.QnCovHatW
