-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.span_nat_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:05.342741+00:00
-- url     : https://prove2.me/submissions/53627df9-42cc-439e-a6a1-da0be14e508d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
import Definitions.Def_Lemmata_MiscLemmasK_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_natCast_ne_zero_oe

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
theorem _root_.solution (ℓ : ℕ) [Fact ℓ.Prime] : Ideal.span {(ℓ : 𝓞 E)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact natCast_ne_zero_oe ℓ
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
