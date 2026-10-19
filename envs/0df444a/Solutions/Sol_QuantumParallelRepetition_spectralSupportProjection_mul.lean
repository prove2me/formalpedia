-- Prove2me | solution 1 for QuantumParallelRepetition.spectralSupportProjection_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/cfb1aeea-319f-4a3d-b5b7-f8a7585748f3

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
    spectralSupportProjection F hF * F = F := by
  change spectralSupportFunctional F hF
      (fun x => if x = 0 then 0 else 1) * F = F
  calc
    spectralSupportFunctional F hF
        (fun x => if x = 0 then 0 else 1) * F =
      spectralSupportFunctional F hF
        (fun x => if x = 0 then 0 else 1) *
          spectralSupportFunctional F hF (fun x => x) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF
          (fun x => (if x = 0 then 0 else 1) * x) :=
      spectralSupportFunctional_mul F hF _ _
    _ = spectralSupportFunctional F hF (fun x => x) :=
      spectralSupportFunctional_congr F hF (by
        intro i
        by_cases hi : hF.isHermitian.eigenvalues i = 0 <;> simp [hi])
    _ = F := spectralSupportFunctional_id F hF
end QuantumParallelRepetition
