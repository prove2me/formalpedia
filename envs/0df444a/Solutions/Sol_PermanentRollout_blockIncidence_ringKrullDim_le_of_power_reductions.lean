-- Prove2me | solution 1 for PermanentRollout.blockIncidence_ringKrullDim_le_of_power_reductions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/f842ba3c-e1bb-4bb8-a80e-e09bfcf6f4f3

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ringKrullDim_le_of_isIntegral
import Theorems.Thm_PermanentRollout_finite_of_totalDegree_power_reductions
import Theorems.Thm_PermanentRollout_blockIncidence_adjoin_column_coordinates
import Theorems.Thm_PermanentRollout_blockIncidenceBase_ringKrullDim

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {b t s d : ℕ} (hd : 3 ≤ d)
    (remainder : BlockIncidenceColumn b t s →
      MvPolynomial (BlockIncidenceColumn b t s)
        (MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ))
    (hdegree : ∀ coordinate, (remainder coordinate).totalDegree < d - 1)
    (hrel :
      letI := blockIncidenceBaseAlgebra b t s d
      ∀ coordinate : BlockIncidenceColumn b t s,
        (Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
          (MvPolynomial.X (coordinate.1, Sum.inr coordinate.2))) ^ (d - 1) =
        MvPolynomial.aeval
          (fun row : BlockIncidenceColumn b t s =>
            Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
              (MvPolynomial.X (row.1, Sum.inr row.2)))
          (remainder coordinate)) :
    ringKrullDim (BlockIncidenceCoordinateRing b t s d) ≤
      ((b * ((2 ^ t - 1) + s * (d - 2)) : ℕ) : WithBot ℕ∞) := by
  letI := blockIncidenceBaseAlgebra b t s d
  letI : Module.Finite
      (MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ)
      (BlockIncidenceCoordinateRing b t s d) :=
    finite_of_totalDegree_power_reductions
      (fun coordinate : BlockIncidenceColumn b t s =>
        Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
          (MvPolynomial.X (coordinate.1, Sum.inr coordinate.2)))
      (d - 1) (by omega) remainder hdegree hrel
      (blockIncidence_adjoin_column_coordinates b t s d)
  letI : Algebra.IsIntegral
      (MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ)
      (BlockIncidenceCoordinateRing b t s d) :=
    Algebra.IsIntegral.of_finite _ _
  exact ringKrullDim_le_of_isIntegral.trans
    (blockIncidenceBase_ringKrullDim b t s d).le
end PermanentRollout
