-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.exists_signVG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:32.419104+00:00
-- url     : https://prove2.me/submissions/402e23a2-99bf-42fd-bd18-931c56863867

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrVGA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) : ∃ s : Bool, Fintype.card (SgIxV ε s) = q0 ε := by
  unfold q0
  rcases le_total (pOf ε) (qOf ε) with h | h
  · refine ⟨true, ?_⟩
    rw [min_eq_left h]
    first
    | (rw [pOf, Fintype.card_subtype])
    | simp [SgIxV, pOf, Fintype.card_subtype]
  · refine ⟨false, ?_⟩
    rw [min_eq_right h]
    first
    | (rw [qOf, Fintype.card_subtype])
    | simp [SgIxV, qOf, Fintype.card_subtype]
end ReciprocityTheory.ChartRestriction.DS.S7
