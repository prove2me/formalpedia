-- Prove2me | solution 1 for QuantumParallelRepetition.fullCoordinateAcceptedPostselectedMass_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/bb1301f9-e2a8-4a54-8f1c-df8ccb0e1354

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_fullCoordinateInsertedHistory_aliceFilter
import Theorems.Thm_QuantumParallelRepetition_fullCoordinateInsertedHistory_bobFilter
import Theorems.Thm_QuantumParallelRepetition_fullCoordinateWeightedInsertedSum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (hL : L ⊆ Finset.univ \ D) :
    fullCoordinateAcceptedPostselectedMass G n S D L i =
      (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) (insert i D)) := by
  classical
  have hLinsert : L ⊆ Finset.univ \ insert i D := by
    intro j hj
    have hjD : j ∉ D := (Finset.mem_sdiff.mp (hL hj)).2
    have hji : j ≠ i := by
      intro he
      exact hiL (he ▸ hj)
    simp [hjD, hji]
  calc
    fullCoordinateAcceptedPostselectedMass G n S D L i =
      ∑ h : FullSubsetHistory X Y n (insert i D) L,
      ∑ α : {j : Fin n // j ∈ insert i D} → A,
      ∑ β : {j : Fin n // j ∈ insert i D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          bornTracePairing S.state.matrix
            (fullHistoryAliceFilter G n S (insert i D) L h α)
            (fullHistoryBobFilter G n S (insert i D) L h β) := by
      have hweighted := fullCoordinateWeightedInsertedSum
        G D L i hiD
        (fun h α β => bornTracePairing S.state.matrix
          (fullHistoryAliceFilter G n S (insert i D) L h α)
          (fullHistoryBobFilter G n S (insert i D) L h β))
      simp_rw [fullCoordinateInsertedHistory_aliceFilter
        G n S D L i hiD hiL,
        fullCoordinateInsertedHistory_bobFilter
          G n S D L i hiD hiL] at hweighted
      simpa [fullCoordinateAcceptedPostselectedMass] using hweighted.symm
    _ = _ := fullSubsetHistory_mass_eq_postselection
      G n S (insert i D) L hLinsert
end QuantumParallelRepetition
