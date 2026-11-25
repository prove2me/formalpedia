-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.polar_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:54.523733+00:00
-- url     : https://prove2.me/submissions/93c6ae96-26a2-4ef8-9233-88ceb1f9475f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_exists_toMK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_polar_UJ


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
variable {ε : Fin n → Bool}
open PolarDecomposition
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ∃ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X ∧ g = toMK k * NormedSpace.exp X := by
  obtain ⟨k, hk, Y, hY, hgk⟩ := polar_UJ (ε := ε) (g := g) hg
  obtain ⟨u, hu⟩ := exists_toMK hk
  exact ⟨u, Y, hY, by rw [hu]; exact hgk⟩
end ReciprocityTheory.ChartRestriction.DS.S7
