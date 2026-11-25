-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.smul_mem_differentIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:27:46.442022+00:00
-- url     : https://prove2.me/submissions/1ec36180-c1ff-4fb0-a019-9f46f73e4e2a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
import Definitions.Def_Lemmata_MiscLemmasK_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_algebraMap_smul_oe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_mem_differentIdeal_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_traceDual_smul

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
theorem _root_.solution (σ : E ≃ₐ[ℚ] E) {x : 𝓞 E} (hx : x ∈ differentIdeal ℤ (𝓞 E)) :
    σ • x ∈ differentIdeal ℤ (𝓞 E) := by
  rw [mem_differentIdeal_iff] at hx ⊢
  rw [Submodule.mem_div_iff_forall_mul_mem] at hx ⊢
  intro y hy
  have h1 := hx (σ.symm y) (traceDual_smul σ.symm hy)
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp h1
  refine Submodule.mem_one.mpr ⟨σ • o, ?_⟩
  rw [algebraMap_smul_oe, ho, algebraMap_smul_oe, map_mul, AlgEquiv.apply_symm_apply]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
