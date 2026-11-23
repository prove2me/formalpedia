-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.lead_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:09:19.089843+00:00
-- url     : https://prove2.me/submissions/61395416-7ca1-4923-8ae6-a067bc652932

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_Minors

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
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (i : ℕ) (hi : i ≤ n) :
    0 < (lead i x).re ∧ (lead i x).im = 0 := by
  have hp := (hx.submatrix (Fin.castLE_injective hi)).det_pos
  unfold lead
  rw [dif_pos hi]
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp hp
  exact ⟨h1, h2.symm⟩
end ReciprocityTheory.ChartRestriction.DS.S7
