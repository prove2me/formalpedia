-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.mem_factors_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:13.206802+00:00
-- url     : https://prove2.me/submissions/b3090782-f62b-4a16-9527-76514a6ac7c9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
import Definitions.Def_Lemmata_MiscLemmasK_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_span_nat_ne_bot

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
theorem _root_.solution (ℓ : ℕ) [Fact ℓ.Prime] {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥)
    (hl : (ℓ : 𝓞 E) ∈ Q) : Q ∈ normalizedFactors (Ideal.span {(ℓ : 𝓞 E)}) := by
  rw [Ideal.mem_normalizedFactors_iff (span_nat_ne_bot ℓ)]
  exact ⟨hQ, (Ideal.span_singleton_le_iff_mem Q).mpr hl⟩
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
