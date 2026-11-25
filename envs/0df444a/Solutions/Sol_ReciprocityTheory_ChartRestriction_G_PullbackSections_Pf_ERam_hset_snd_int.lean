-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.hset_snd_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:27:36.912222+00:00
-- url     : https://prove2.me/submissions/28e92514-c161-459a-8f55-5b330cfcff97

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamLift

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [Field k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution {h : PS k 2 d} {X : Fin d → k} (hX : ((0 : Fin d → k), X) ∈ Hset (R := R) k h) (_hinj : Function.Injective (algebraMap R k)) :
    ∀ i, X i ∈ (algebraMap R k).range := by
  intro i
  obtain ⟨u, φ, hξ⟩ := hX
  have h1 := congrArg Prod.fst hξ
  have h2 := congrArg Prod.snd hξ
  simp only at h1 h2
  rw [← h1, Matrix.mulVec_zero] at h2
  simp only [Pi.zero_apply, sub_zero] at h2
  exact ⟨φ i, (congrFun h2 i).symm⟩
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
