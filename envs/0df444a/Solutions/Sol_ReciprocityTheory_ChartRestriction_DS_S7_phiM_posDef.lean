-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.phiM_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:34.858068+00:00
-- url     : https://prove2.me/submissions/ac1b2dcf-b400-4ad2-95d5-f31831f9136f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_Minors
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lead_posDef


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
theorem _root_.solution (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    0 < (PhiM μ x).re ∧ (PhiM μ x).im = 0 := by
  have hpos : ∀ i : Fin n, 0 < (lead ((i : ℕ) + 1) x).re :=
    fun i => (lead_posDef hx _ (by have := i.2; omega)).1
  have hr : ∀ i : Fin n, lead ((i : ℕ) + 1) x = ((lead ((i : ℕ) + 1) x).re : ℂ) := by
    intro i
    apply Complex.ext
    · simp
    · simp [(lead_posDef hx ((i : ℕ) + 1) (by have := i.2; omega)).2]
  have hP : PhiM μ x = ((∏ i : Fin n, (lead ((i : ℕ) + 1) x).re ^ (-(μ i - muNext μ i)) : ℝ) : ℂ) := by
    unfold PhiM
    push_cast
    exact Finset.prod_congr rfl fun i _ => by rw [← hr i]
  rw [hP, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Finset.prod_pos fun i _ => zpow_pos (hpos i) _, rfl⟩
end ReciprocityTheory.ChartRestriction.DS.S7
