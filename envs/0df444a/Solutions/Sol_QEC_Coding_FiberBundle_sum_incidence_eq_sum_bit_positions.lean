-- Prove2me | solution 1 for QEC.Coding.FiberBundle.sum_incidence_eq_sum_bit_positions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:30:56.02847+00:00
-- url     : https://prove2.me/submissions/5f7bd86e-e833-47f0-9003-459285f63b8f

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {M : Type*} [AddCommMonoid M]
    (f : ClassicalWeightReduction.Incidence R → M) :
    (∑ e, f e) =
      ∑ b : baseOne,
        ∑ i : Fin (Fintype.card
          (ClassicalWeightReduction.BitNeighbor R b)),
          f (ClassicalWeightReduction.bitIncidenceAt R b i) := by
  calc
    (∑ e, f e) =
        ∑ s : ClassicalWeightReduction.BitPositionSigma R,
          f ((incidenceBitPositionEquiv D).symm s) := by
      exact (Equiv.sum_comp (incidenceBitPositionEquiv D).symm f).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      rfl
end QEC.Coding.FiberBundle
