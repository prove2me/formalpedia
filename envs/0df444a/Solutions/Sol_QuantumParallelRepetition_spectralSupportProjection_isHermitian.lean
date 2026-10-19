-- Prove2me | solution 1 for QuantumParallelRepetition.spectralSupportProjection_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/eb5dc050-df1d-468e-bd7e-f06d4c1f97b7

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (spectralSupportProjection F hF).IsHermitian :=
  spectralSupportFunctional_isHermitian F hF _
end QuantumParallelRepetition
