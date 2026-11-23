-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.isMu_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:07.103014+00:00
-- url     : https://prove2.me/submissions/671566ec-bc5f-4617-b2f8-4c90d530e9fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExistsMu
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiMExpFormula

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {lam : Fin n → ℝ} {μ μ' : Fin n → ℤ} (hμ : IsMu lam μ) (hμ' : IsMu lam μ') : μ' = μ :=
  funext fun a => by
    have h2 : ((μ' a : ℤ) : ℝ) = ((μ a : ℤ) : ℝ) := (hμ' a).trans (hμ a).symm
    exact_mod_cast h2
end ReciprocityTheory.ChartRestriction.DS.S7
