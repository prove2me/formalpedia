-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.killB_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:48.200825+00:00
-- url     : https://prove2.me/submissions/08a0c04b-ec35-4468-ac51-365bf5b70293

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HasympAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (T : Finset K) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) :
    killB T (monomial m c : MRing ι) = if (∃ p, p.1 ∈ T ∧ m p ≠ 0) then 0 else monomial m c := by
  unfold killB
  rw [MvPolynomial.aeval_monomial]
  split_ifs with h
  · obtain ⟨p, hpT, hp⟩ := h
    apply mul_eq_zero_of_right
    rw [Finsupp.prod]
    apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hp)
    simp [hpT, hp]
  · push_neg at h
    rw [Finsupp.prod]
    have hc : ∀ p ∈ m.support, (if p.1 ∈ T then (0 : MRing ι) else X p) ^ m p = X p ^ m p := by
      intro p hp
      rw [if_neg]
      intro hT
      exact (Finsupp.mem_support_iff.mp hp) (h p hT)
    rw [Finset.prod_congr rfl hc, ← Finsupp.prod, MvPolynomial.monomial_eq, MvPolynomial.algebraMap_eq]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
