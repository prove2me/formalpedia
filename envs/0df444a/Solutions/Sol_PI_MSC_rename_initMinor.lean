-- Prove2me | solution 1 for PI.MSC.rename_initMinor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:06:00.896341+00:00
-- url     : https://prove2.me/submissions/ea3a205f-6bcd-493e-b5c4-e127abfe91df

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MinorSpanCompl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ExistsCoeffNeZeroOfMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_RenameInitMinor
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.MSC
namespace PI.MSC
theorem _root_.solution (R : Type) [CommRing R] (N n s : ℕ) (hs : s ≤ n) (I : Fin s ↪o Fin N) :
    rename (phi N n) (initMinor R (r := N) (n := n) (fun p => I p) hs) = PI.minorX R N s I := by
  unfold initMinor PI.minorX
  rw [AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext i k
  simp [phi, Matrix.transpose_apply, rename_X]
end PI.MSC
