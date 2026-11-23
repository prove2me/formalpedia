-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.DS.S7.IdA.isOpen_omega
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:09.1284+00:00
-- url     : https://prove2.me/submissions/ac23ef7d-c7ce-4451-8717-a8b008b107df

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IdThmA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_contDiff_lead


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
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.IdA
namespace ReciprocityTheory.ChartRestriction.DS.S7.IdA
theorem _root_.solution : IsOpen (OmegaSet n) := by
  have e : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [e]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun (contDiff_lead (m := 0) _).continuous continuous_const
end ReciprocityTheory.ChartRestriction.DS.S7.IdA
