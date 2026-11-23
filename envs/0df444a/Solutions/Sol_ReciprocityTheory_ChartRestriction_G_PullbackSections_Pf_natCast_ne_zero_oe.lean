-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.natCast_ne_zero_oe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:36.857652+00:00
-- url     : https://prove2.me/submissions/76408f61-7b30-4d00-b5d6-f4103d96ccd2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
import Definitions.Def_Lemmata_MiscLemmasK_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
theorem _root_.solution (ℓ : ℕ) [hℓ : Fact ℓ.Prime] : (ℓ : 𝓞 E) ≠ 0 := by
  intro h
  have h2 := congrArg (algebraMap (𝓞 E) E) h
  rw [map_natCast, map_zero, Nat.cast_eq_zero] at h2
  exact hℓ.out.ne_zero h2
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
