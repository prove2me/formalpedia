-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/d9ce62bc-1a19-4de8-8b55-3039526b8350

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    (B N d L m : ℕ)
    (U : Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L) ℂ)
    (a b : DSVDensityRationalPublicLogPhaseHistoryLocalIndex
      B N d L) (i j : Fin m) :
    dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
      B N d L m U
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m (a, i))
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m (b, j)) =
      if i = j then U a b else 0 := by
  classical
  change
    (Matrix.reindex
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m)
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m)
      (U.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)))
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m (a, i))
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m (b, j)) = _
  simp [Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
end QuantumParallelRepetition
