-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.affCoord_eq_of_sameOrbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:34.192117+00:00
-- url     : https://prove2.me/submissions/60de4b15-ee59-4b1f-b970-a13ea3b1e78e

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (p : (k : K) → ι k) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  show c q.1 * z' q / (c q.1 * z' ⟨q.1, p q.1⟩) = z' q / z' ⟨q.1, p q.1⟩
  exact mul_div_mul_left (z' q) (z' ⟨q.1, p q.1⟩) (hc q.1)
end ReciprocityTheory.AnForm.R
