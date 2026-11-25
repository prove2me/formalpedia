-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.multiset_prod_sub_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:29:11.211998+00:00
-- url     : https://prove2.me/submissions/559567a1-d8fb-4ae9-94b0-f08bfacbe114

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution {S ι : Type*} [CommRing S] (t : S) (k : ℕ) (x y : ι → S)
    (hx : ∀ i, t ∣ x i) (hy : ∀ i, t ∣ y i) (hxy : ∀ i, t ^ k ∣ x i - y i) :
    ∀ s : Multiset ι, s ≠ 0 →
      t ^ (k + Multiset.card s - 1) ∣ (s.map x).prod - (s.map y).prod := by

  have hQ : ∀ u : Multiset ι, t ^ Multiset.card u ∣ (u.map y).prod := by
    intro u
    refine Multiset.induction_on u ?_ ?_
    · simp
    · intro b u ihu
      rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ']
      exact mul_dvd_mul (hy b) ihu
  intro s
  refine Multiset.induction_on s ?_ ?_
  · intro h
    exact absurd rfl h
  · intro a s ih _
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.prod_cons]
    by_cases hs : s = 0
    · subst hs
      simpa using hxy a
    · have hc : Multiset.card s ≠ 0 := fun h => hs (Multiset.card_eq_zero.mp h)
      have h1 := ih hs
      have key : x a * (s.map x).prod - y a * (s.map y).prod
          = x a * ((s.map x).prod - (s.map y).prod) + (x a - y a) * (s.map y).prod := by ring
      have e : k + (Multiset.card s + 1) - 1 = (k + Multiset.card s - 1) + 1 := by omega
      rw [key, e]
      refine dvd_add ?_ ?_
      · rw [pow_succ']
        exact mul_dvd_mul (hx a) h1
      · have e2 : k + Multiset.card s - 1 + 1 = k + Multiset.card s := by omega
        rw [e2, pow_add]
        exact mul_dvd_mul (hxy a) (hQ s)
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
