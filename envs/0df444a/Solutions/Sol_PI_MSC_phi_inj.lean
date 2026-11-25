-- Prove2me | solution 1 for PI.MSC.phi_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:10:01.075826+00:00
-- url     : https://prove2.me/submissions/412e2a42-4297-48f4-a4cb-647c01b57d4b

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
theorem _root_.solution (N n : ℕ) : Function.Injective (phi N n) := by
  rintro ⟨a, s⟩ ⟨a', s'⟩ h
  simp only [phi, Prod.mk.injEq] at h
  ext
  · exact congrArg Fin.val h.2
  · exact h.1
end PI.MSC
