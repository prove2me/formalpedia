-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.of_mem_factors_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:27:38.196075+00:00
-- url     : https://prove2.me/submissions/6d056af5-a918-4952-a9d2-95b15b50d8bf

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
theorem _root_.solution (ℓ : ℕ) [Fact ℓ.Prime] {Q : Ideal (𝓞 E)}
    (hQ : Q ∈ normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})) : Q.IsPrime ∧ Q ≠ ⊥ ∧ (ℓ : 𝓞 E) ∈ Q := by
  have hQ' := (Ideal.mem_normalizedFactors_iff (span_nat_ne_bot ℓ)).mp hQ
  refine ⟨hQ'.1, ?_, (Ideal.span_singleton_le_iff_mem Q).mp hQ'.2⟩
  intro h0
  rw [h0, le_bot_iff] at hQ'
  exact span_nat_ne_bot ℓ hQ'.2
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
