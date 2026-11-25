-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.blockDeg_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:04:07.899169+00:00
-- url     : https://prove2.me/submissions/86d9d620-e4f1-4f76-becd-33b25db63918

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (q : Σ k, ι k) (m : ℕ) (k' : K) :
    ∑ i, (Finsupp.single q m : (Σ k, ι k) →₀ ℕ) ⟨k', i⟩ = if q.1 = k' then m else 0 := by
  obtain ⟨k0, i0⟩ := q
  by_cases h : k0 = k'
  · subst h
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · simp [Finsupp.single_apply, Sigma.mk.inj_iff, h]
end ReciprocityTheory.ChartRestriction.G.Geo
