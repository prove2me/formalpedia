-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.filteredBranchOperatorSum_eq_sum_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:26:23.351108+00:00
-- url     : https://prove2.me/submissions/a0cd6df3-5734-48b1-aa7f-d83f9740c868

import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Branches_FilteredBranchMeasurement

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.FiniteInstrument
open Classical
open scoped BigOperators
universe u v w x y
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {mu : Type x} [Fintype mu]
variable {Xi : Type y} [Fintype Xi]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
  [FiniteQuantumSystem L]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (I : FiniteInstrument kappa Omega H K)
    (predicate : Omega -> Prop) [DecidablePred predicate]
    (A : Operator H) :
    filteredBranchOperatorSum I predicate A =
      ∑ outcome ∈ Finset.univ.filter predicate,
        I.branchOperator outcome A := by
  classical
  unfold filteredBranchOperatorSum
  rw [Finset.sum_filter]
end QEC.Semantics.FiniteInstrument
