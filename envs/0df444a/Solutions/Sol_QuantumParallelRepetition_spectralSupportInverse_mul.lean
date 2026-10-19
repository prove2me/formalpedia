-- Prove2me | solution 1 for QuantumParallelRepetition.spectralSupportInverse_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/d06b44ae-4c1b-42b8-bc60-4a21565d5c67

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
    spectralSupportInverse F hF * F =
      spectralSupportProjection F hF := by
  change spectralSupportFunctional F hF (fun x => x⁻¹) * F =
    spectralSupportFunctional F hF (fun x => if x = 0 then 0 else 1)
  calc
    spectralSupportFunctional F hF (fun x => x⁻¹) * F =
        spectralSupportFunctional F hF (fun x => x⁻¹) *
          spectralSupportFunctional F hF (fun x => x) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF (fun x => x⁻¹ * x) :=
      spectralSupportFunctional_mul F hF _ _
    _ = _ := spectralSupportFunctional_congr F hF (by
      intro i
      by_cases hi : hF.isHermitian.eigenvalues i = 0
      · simp [hi]
      · simp [hi])
end QuantumParallelRepetition
