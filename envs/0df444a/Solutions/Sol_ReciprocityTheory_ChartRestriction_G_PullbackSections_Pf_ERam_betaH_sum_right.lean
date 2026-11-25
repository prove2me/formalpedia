-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.betaH_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:27:10.537846+00:00
-- url     : https://prove2.me/submissions/b5b373df-cab8-4d4e-9df7-d67068a0021f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [Field k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution {ι : Type} (s : Finset ι) (ξ : (Fin d → k) × (Fin d → k)) (f : ι → (Fin d → k) × (Fin d → k)) :
    betaH k ξ (∑ i ∈ s, f i) = ∑ i ∈ s, betaH k ξ (f i) := by
  simp only [betaH, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_comm
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
