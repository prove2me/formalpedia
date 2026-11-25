-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKH.isBlock_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:47.681809+00:00
-- url     : https://prove2.me/submissions/c908b58a-021e-4b95-a435-9f273b7dcdb2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_TauPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LowMinusUpExpand

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
variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.InfKH
variable {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.InfKH
theorem _root_.solution {a b : Fin n} (h : ε b = ε a) : IsBlock ε (Matrix.single a b (1 : ℂ)) := by
  intro a' b' hne
  by_cases h' : a = a' ∧ b = b'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd h.symm hne
  · first
    | rw [Matrix.single_apply, if_neg h']
    | simp [Matrix.single_apply, h']
    | (simp only [Matrix.single_apply]
       exact if_neg h')
end ReciprocityTheory.ChartRestriction.DS.S7.InfKH
