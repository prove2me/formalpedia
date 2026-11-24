-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_X__ddfde4c79f12
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:53.045165+00:00
-- url     : https://prove2.me/submissions/4653a55b-88e8-481c-8226-755c72dd6b95

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogIdealChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogX

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution [DecidableEq K] (b : K) (i : ι b) :
    IsMultiHomog (X ⟨b, i⟩ : MRing ι) (Pi.single b 1) := by
  intro m hm k
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hk : k = b
  · subst hk
    simp only [Pi.single_eq_same]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      apply Finsupp.single_eq_of_ne
      intro h
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      exact hj (by first | exact h.symm | exact h)
    · intro h; exact absurd (Finset.mem_univ i) h
  · simp [Finsupp.single_apply, hk, Ne.symm hk]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
