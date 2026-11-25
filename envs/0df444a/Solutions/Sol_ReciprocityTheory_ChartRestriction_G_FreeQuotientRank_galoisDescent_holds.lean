-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.galoisDescent_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:05:43.417269+00:00
-- url     : https://prove2.me/submissions/442a359a-47ad-4b99-b01f-61567440b0ad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_DescPf_sum_galAct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_DescPf_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution : GaloisDescentStatement := by
  intro K K₂ V _ _ _ _ _ _ _ W hW
  classical
  apply le_antisymm
  · intro w hw
    rw [DescPf.expand (Module.finBasis K K₂) w]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    simp only [SetLike.mem_coe, kPoints, Submodule.mem_comap, Submodule.restrictScalars_mem,
      TensorProduct.mk_apply]
    rw [← DescPf.sum_galAct]
    exact Submodule.sum_mem _ fun σ _ => hW σ _ (W.smul_mem _ hw)
  · rw [baseSpan, Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    simpa only [SetLike.mem_coe, kPoints, Submodule.mem_comap, Submodule.restrictScalars_mem,
      TensorProduct.mk_apply] using hu
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
