-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.quotCore_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:33:45.252194+00:00
-- url     : https://prove2.me/submissions/99af7816-d9ae-42e0-ab13-b06b084eafee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreLocalPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreGlobPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCorePf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_qcoreGlobal_holds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_qcoreLocal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution (hL : QuotLocalStatement) : QuotCoreStatement := by
  intro hLD K K₁ V _ _ _ _ _ _ _ _ _ _ M hfg hspan W θ hθ c hker be s hbe _ hs hint supN a Bθ Carch
    Bdeg hconj hshort harch hdeg
  obtain ⟨hdet, hloc⟩ :=
    qcoreLocal hLD hL K K₁ V M hfg hspan W θ hθ c hker be s hbe hs hint
  obtain ⟨hsupp, hglob⟩ :=
    qcoreGlobal_holds K K₁ V M _ θ c hdet s hs supN a Bθ Carch Bdeg hconj hshort harch hdeg
  refine ⟨Finsupp.ofSupportFinite _ hsupp, ?_, ?_⟩
  · intro la
    obtain ⟨ℓ, hℓ, hle⟩ := hloc la
    exact ⟨ℓ, hℓ, hle⟩
  · have hsum : ((Finsupp.ofSupportFinite _ hsupp).sum fun la v => v * logN la) =
        ∑ᶠ la : HeightOneSpectrum (𝓞 K), nnFun (K := K) (detCT c θ) s la * logN la := by
      rw [finsum_eq_sum_of_support_subset (s := hsupp.toFinset)]
      · rfl
      · intro la hla
        rw [Set.Finite.coe_toFinset]
        exact Function.support_mul_subset_left _ _ hla
    rw [hsum]
    exact hglob
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
