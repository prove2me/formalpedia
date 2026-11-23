-- Prove2me | solution 1 for PI.EF.order_Lent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:40.502797+00:00
-- url     : https://prove2.me/submissions/6719c691-c143-4699-9e6d-c211a6cfa499

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Theorems.Thm_PI_EF_Lent_of_ne
import Theorems.Thm_PI_EF_Lent_eventuallyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt (Lent χ) s = analyticOrderNatAt (LFunction χ) s := by
  by_cases h : χ = 1
  · have hL : AnalyticAt ℂ (LFunction χ) s := by
      apply DifferentiableOn.analyticAt (s := {z | z ≠ 1})
      · intro z hz
        exact (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
      · exact isOpen_ne.mem_nhds hs
    have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
    have h0 : analyticOrderAt (fun z : ℂ => z - 1) s = 0 :=
      h1.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hs)
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr (Lent_eventuallyEq h hs), analyticOrderAt_mul h1 hL, h0, zero_add]
  · rw [Lent_of_ne h]
end PI.EF
