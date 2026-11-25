-- Prove2me | solution 1 for PI.MSC.initMinor_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:50:48.259946+00:00
-- url     : https://prove2.me/submissions/e5ac7dcc-7bbf-4c2a-be85-c9ce93414f00

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
theorem _root_.solution (R : Type) [CommRing R] {r n s s' : ℕ} (h : s' = s) (I : Fin s → Fin r)
    (hs : s ≤ n) (hs' : s' ≤ n) :
    initMinor R (I ∘ Fin.cast h) hs' = initMinor R I hs := by
  subst h
  rfl
end PI.MSC
