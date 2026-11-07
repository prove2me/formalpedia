-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.card_qubitIndex
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T07:52:01.651224+00:00
-- url     : https://prove2.me/submissions/3a78b00c-5981-4035-bfc3-4f592268ba1f

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped BigOperators
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)

theorem solution :
    Fintype.card (QubitIndex xOne xTwo classicalBit classicalCheck) =
      Fintype.card xOne * Fintype.card classicalBit +
        Fintype.card xTwo * Fintype.card classicalCheck := by
  simp [QubitIndex, Fintype.card_sum, Fintype.card_prod]
