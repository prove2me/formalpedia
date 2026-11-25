-- Prove2me | solution 1 for PI.DvRows.dvProjRows_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:03:10.417287+00:00
-- url     : https://prove2.me/submissions/83dbccb5-8145-49df-95b5-a25041696c96

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_ValLeOneOfMemRange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Development
import Theorems.Thm_PI_DvRows_partA
import Theorems.Thm_PI_DvRows_partC


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
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
namespace PI.DvRows
theorem _root_.solution (hB : PartB) : PI.Dv.division_rows_base_level := by
  intro K _ _ _ _ _ A e n h hS hP hH hC hD U hU
  exact ⟨fun w k hk => partA A e n h hP hH hD U hU w k hk,
    fun γ hγ => hB K A e n h hS hP hH hC hD U hU γ hγ, partC A e U⟩
end PI.DvRows
