-- Prove2me | solution 1 for QuantumParallelRepetition.mul_spectralSupportInverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/cb96505d-2063-469c-89a2-0d2466296e73

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
    F * spectralSupportInverse F hF =
      spectralSupportProjection F hF := by
  change F * spectralSupportFunctional F hF (fun x => x⁻¹) =
    spectralSupportFunctional F hF (fun x => if x = 0 then 0 else 1)
  calc
    F * spectralSupportFunctional F hF (fun x => x⁻¹) =
        spectralSupportFunctional F hF (fun x => x) *
          spectralSupportFunctional F hF (fun x => x⁻¹) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF (fun x => x * x⁻¹) :=
      spectralSupportFunctional_mul F hF _ _
    _ = _ := spectralSupportFunctional_congr F hF (by
      intro i
      by_cases hi : hF.isHermitian.eigenvalues i = 0
      · simp [hi]
      · simp [hi])
end QuantumParallelRepetition
