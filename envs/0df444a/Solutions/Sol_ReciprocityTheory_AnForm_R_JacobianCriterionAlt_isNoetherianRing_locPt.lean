-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.isNoetherianRing_locPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:08:41.622153+00:00
-- url     : https://prove2.me/submissions/6145eb22-001b-40ae-b601-1096b7974f28

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt
open MvPolynomial IsLocalRing
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R.JacobianCriterionAlt
theorem _root_.solution (p : Fin n → ℂ) : IsNoetherianRing (localization₂ p) :=
  IsLocalization.isNoetherianRing (ptI p).primeCompl _ inferInstance
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
