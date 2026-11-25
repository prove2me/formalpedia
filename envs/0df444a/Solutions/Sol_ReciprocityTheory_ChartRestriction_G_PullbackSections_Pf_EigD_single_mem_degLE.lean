-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.single_mem_degLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:36:09.49181+00:00
-- url     : https://prove2.me/submissions/583c2320-8a65-4de9-8efa-5fc36f48edd9

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SingleMemDegLE

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
open MvPolynomial CategoryTheory Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G
attribute [local instance] Over.cartesianMonoidalCategory
variable {V : Type} [CommRing V]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (ℓ : ι) : Finsupp.single ℓ 1 ∈ degLE (ι := ι) 1 := by
  simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨⟨fun i => if i = ℓ then 1 else 0, ?_⟩, ?_⟩
  · ext i
    by_cases h : i = ℓ
    · subst h; simp
    · simp [h, Finsupp.single_apply, Ne.symm h]
  · simp [Finsupp.sum_single_index]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
