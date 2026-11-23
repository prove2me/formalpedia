-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.rho_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:15.079464+00:00
-- url     : https://prove2.me/submissions/9ab5a5bf-e75f-4fe6-9244-c9f7199091d2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
open NumberField Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows.GramDeterminantPositive
theorem _root_.solution (φ : K →+* ℂ) (x : K) : rho φ x = star (φ (star x)) := rfl
end PI.DvRows.GramDeterminantPositive
