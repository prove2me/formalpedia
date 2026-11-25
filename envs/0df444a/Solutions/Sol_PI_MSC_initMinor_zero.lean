-- Prove2me | solution 1 for PI.MSC.initMinor_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:50:51.70545+00:00
-- url     : https://prove2.me/submissions/74019c49-9f5b-4f76-b8f0-59a35bc4ee52

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.MSC
namespace PI.MSC
theorem _root_.solution (R : Type) [CommRing R] {r n s : ℕ} (h : s = 0) (I : Fin s → Fin r)
    (hs : s ≤ n) : initMinor R I hs = 1 := by
  subst h
  simp [initMinor]
end PI.MSC
