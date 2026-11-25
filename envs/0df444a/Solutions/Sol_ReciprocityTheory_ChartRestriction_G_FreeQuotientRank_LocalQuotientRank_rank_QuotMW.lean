-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank.rank_QuotMW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:52.420808+00:00
-- url     : https://prove2.me/submissions/72b9fe3a-67e3-4b9b-bcd1-da9f03f0e157

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FreeQuotPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalQuotientRank
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_LocalQuotientRank_rank_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank
open NumberField Module
open scoped TensorProduct
variable {K K₁ V : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank
theorem _root_.solution (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hspan : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V) :
    Module.finrank (𝓞 K) (QuotMW M W) + Module.finrank K W = Module.finrank K V := by
  have h := rank_quot (F := K) M hM W
  rw [hspan, top_inf_eq, finrank_top] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank
