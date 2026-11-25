-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapPhi.isGlRep_negE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:57:43.761802+00:00
-- url     : https://prove2.me/submissions/9e9aa830-4148-4467-a566-f2e9dcfd523f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_CapPhi_single_mul_single__6f664d746993
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_isGlRep_eOp


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
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
namespace ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
theorem _root_.solution : IsGlRep (negE (n := n)) := by
  apply isGlRep_eOp
  intro a b c d
  simp only [neg_mul_neg, single_mul_single']
  split_ifs <;> abel
end ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
