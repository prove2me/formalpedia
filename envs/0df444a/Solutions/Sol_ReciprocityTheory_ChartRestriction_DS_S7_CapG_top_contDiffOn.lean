-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapG.top_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:33:12.837703+00:00
-- url     : https://prove2.me/submissions/da8da295-e0b7-47e8-bb17-2db33fb4cc7a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ChainHSlice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LholClmEventually
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_TopContDiffOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GelfandGA_lhol_contDiffOn


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
open ReciprocityTheory.ChartRestriction.DS.S7.CapG
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace ReciprocityTheory.ChartRestriction.DS.S7.CapG
theorem _root_.solution {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U)
    {G : Matrix (Fin n) (Fin n) ℂ → E} (hG : ContDiffOn ℂ ∞ G U) (u : ℂ) (a b : Fin n) :
    ContDiffOn ℂ ∞ (Formalism.QuantumDeterminants.Top negL u a b G) U := by
  have h2 : ContDiffOn ℂ ∞ (negL a b G) U := (GelfandGA.lhol_contDiffOn hU hG _).neg
  unfold Formalism.QuantumDeterminants.Top
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte]
    exact (hG.const_smul u).add h2
  · simp only [hab, ↓reduceIte, zero_add]
    exact h2
end ReciprocityTheory.ChartRestriction.DS.S7.CapG
