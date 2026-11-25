-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.sum_single_toList
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:27:25.564903+00:00
-- url     : https://prove2.me/submissions/33c28724-0a2c-460b-933d-d2a905700d3a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
theorem _root_.solution (k : σ →₀ ℕ) :
    ((Finsupp.toMultiset k).toList.map fun q => Finsupp.single q 1).sum = k := by
  classical
  have h : ∀ t : Multiset σ, (t.map fun q => Finsupp.single q 1).sum = Multiset.toFinsupp t := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp
    | cons a t ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, ← Multiset.singleton_add, Multiset.toFinsupp_add,
        Multiset.toFinsupp_singleton]
  first
    | (rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList, h, Finsupp.toMultiset_toFinsupp])
    | (have h2 := h (Finsupp.toMultiset k)
       rw [Finsupp.toMultiset_toFinsupp] at h2
       rw [← h2, ← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList])
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
