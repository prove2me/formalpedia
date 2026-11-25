-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GelfandGA.opPow_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:08.093413+00:00
-- url     : https://prove2.me/submissions/2c59e326-891c-42db-8bea-d1ceeee7379b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsOfFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGA
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
open ReciprocityTheory.ChartRestriction.DS.S7.GelfandGA
local notation "𝕄" => Fin n → Fin n → ℂ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.S7.GelfandGA
theorem _root_.solution {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U)
    {F : Matrix (Fin n) (Fin n) ℂ → E} (hF : ContDiffOn ℂ ∞ F U)
    (Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) :
    ∀ j a b, ContDiffOn ℂ ∞ (opPow (fun a b => Lhol (Y a b)) j a b F) U := by
  intro j
  induction j with
  | zero =>
    intro a b
    simp only [opPow]
    split_ifs
    · exact hF
    · exact contDiffOn_const
  | succ k ih =>
    intro a b
    simp only [opPow]
    rw [Finset.sum_fn]
    exact ContDiffOn.sum fun c _ => lhol_contDiffOn hU (ih c b) (Y a c)
end ReciprocityTheory.ChartRestriction.DS.S7.GelfandGA
