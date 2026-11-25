-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.smul_differentIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:33:00.58936+00:00
-- url     : https://prove2.me/submissions/ba56ff4f-8776-4fe9-aa42-b9a7ae4d1bfe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
import Definitions.Def_Lemmata_MiscLemmasK_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_smul_mem_differentIdeal

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
theorem _root_.solution (σ : E ≃ₐ[ℚ] E) : σ • differentIdeal ℤ (𝓞 E) = differentIdeal ℤ (𝓞 E) := by
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro h
    simpa using smul_mem_differentIdeal σ h
  · intro h
    exact smul_mem_differentIdeal σ⁻¹ h
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
