-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.mem_differentIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:13.023238+00:00
-- url     : https://prove2.me/submissions/d6a571da-3a7c-49c1-8448-9eb11b4b24a5

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
theorem _root_.solution (x : 𝓞 E) : x ∈ differentIdeal ℤ (𝓞 E) ↔
    algebraMap (𝓞 E) E x ∈ (1 / Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) : Submodule (𝓞 E) E) := by
  rw [← coeSubmodule_differentIdeal ℤ ℚ, IsLocalization.mem_coeSubmodule]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, e⟩
    rwa [← (IsFractionRing.injective (𝓞 E) E) e]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
