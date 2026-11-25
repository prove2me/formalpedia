-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.count_span_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:27:28.122332+00:00
-- url     : https://prove2.me/submissions/ab85a576-48a0-45b9-b2b3-0f3d0d0e13c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
import Definitions.Def_Lemmata_MiscLemmasK_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_natCast_ne_zero_oe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_mem_factors_span

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
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
theorem _root_.solution (E : Type) [Field E] [NumberField E] (ℓ : ℕ) (hℓ : ℓ.Prime) {P : Ideal (𝓞 E)}
    (hP : P.IsPrime) (hl : (ℓ : 𝓞 E) ∈ P) : 0 < (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).count P := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact natCast_ne_zero_oe (E := E) ℓ (Ideal.mem_bot.mp hl)
  exact Multiset.count_pos.mpr (mem_factors_span ℓ hP hP0 hl)
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
