-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:25:41.376415+00:00
-- url     : https://prove2.me/submissions/cd8de411-eb08-4fea-9b2a-2443d5ef2682

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_prod

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
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (i : ∀ k, ι k) (e : K → ℕ) : IsMultiHomog (xpow i e) e := by
  classical
  have hX : ∀ k, IsMultiHomog (X ⟨k, i k⟩ : MRing ι) (Pi.single k 1) := by
    intro k m hm k'
    rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
    subst hm
    by_cases hk : k' = k
    · subst hk
      rw [Finset.sum_eq_single (i k')]
      · simp
      · intro j _ hj
        simp [Finsupp.single_apply, Sigma.mk.inj_iff, Ne.symm hj]
      · simp
    · simp [Finsupp.single_apply, Sigma.mk.inj_iff, hk, Ne.symm hk]
  have h := isMultiHomog_prod Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι) ^ e k)
    (fun k => e k • Pi.single k 1) (fun k => isMultiHomog_pow (hX k) (e k))
  have he : (∑ k, e k • Pi.single k 1 : K → ℕ) = e := by
    ext k'
    simp [Finset.sum_apply, Pi.single_apply]
  rw [he] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
