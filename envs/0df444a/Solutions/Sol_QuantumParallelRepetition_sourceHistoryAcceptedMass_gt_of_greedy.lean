-- Prove2me | solution 1 for QuantumParallelRepetition.sourceHistoryAcceptedMass_gt_of_greedy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/9bf5eb30-24d8-43b1-9504-e7418414feb8

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_sourceHistoryAcceptedMass_eq_remaining_average

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card)
    {η : ℝ}
    (hgreedy :
      (∑ i ∈ Finset.univ \ D,
        FiniteEventLaw.failureMass
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D i) <
        ((Finset.univ \ D).card : ℝ) *
          (η * (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent
              (repeatedCoordinateWin G n) D))) :
    (1 - η) *
        (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) D) <
      sourceHistoryAcceptedMass G n S D := by
  classical
  let p : ℝ := (strategyEventLaw (G.repeat n) S).eventMass
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
  have hmreal : 0 < ((Finset.univ \ D).card : ℝ) := by
    exact_mod_cast hm
  have hsub := Finset.sum_subtype (F := inferInstance)
    (Finset.univ \ D)
    (fun i : Fin n => Iff.rfl)
    (fun i : Fin n => (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
        (insert i D)))
  have hfails :
      (∑ i ∈ Finset.univ \ D,
        FiniteEventLaw.failureMass
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D i) =
        ((Finset.univ \ D).card : ℝ) * p -
          (∑ i ∈ Finset.univ \ D,
            (strategyEventLaw (G.repeat n) S).eventMass
              (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
                (insert i D))) := by
    simp [FiniteEventLaw.failureMass, p, Finset.sum_sub_distrib]
  rw [sourceHistoryAcceptedMass_eq_remaining_average]
  rw [← hsub]
  apply (lt_div_iff₀ hmreal).mpr
  change (1 - η) * p * ((Finset.univ \ D).card : ℝ) < _
  change
    (∑ i ∈ Finset.univ \ D,
      FiniteEventLaw.failureMass
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D i) <
      ((Finset.univ \ D).card : ℝ) * (η * p) at hgreedy
  nlinarith [hgreedy, hfails]
end QuantumParallelRepetition
