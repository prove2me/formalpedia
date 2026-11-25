-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.toMultiset_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:28:09.058717+00:00
-- url     : https://prove2.me/submissions/cfcf8743-ba86-449a-964d-cd33efbdb95e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {ι : Type} [Fintype ι] (u : ι → Fin g → ℂ) (m : ι →₀ ℕ) :
    (Finsupp.toMultiset m).map u = ∑ l, Multiset.replicate (m l) (u l) := by
  refine Finsupp.induction_linear m ?_ ?_ ?_
  · simp
  · intro f₁ f₂ h₁ h₂
    rw [map_add, Multiset.map_add, h₁, h₂]
    simp [Multiset.replicate_add, Finset.sum_add_distrib]
  · intro a b
    rw [Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.map_singleton, Multiset.nsmul_singleton]
    rw [Finset.sum_eq_single a]
    · simp
    · intro l _ hl
      simp [Finsupp.single_apply, Ne.symm hl]
    · intro h
      exact absurd (Finset.mem_univ a) h
end ReciprocityTheory.ChartRestriction.G.PullbackSections
