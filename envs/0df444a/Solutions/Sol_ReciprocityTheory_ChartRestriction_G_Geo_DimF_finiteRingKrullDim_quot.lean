-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.DimF.finiteRingKrullDim_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:49.816672+00:00
-- url     : https://prove2.me/submissions/c05f7b8c-30f9-4fcc-ad7f-c46039eb2784

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_IsCMOfIsRegularLocalRing
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF
namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF
theorem _root_.solution {B : Type*} [CommRing B] [FiniteRingKrullDim B] (q : Ideal B)
    [q.IsPrime] : FiniteRingKrullDim (B ⧸ q) := by
  have hle : ringKrullDim (B ⧸ q) ≤ ringKrullDim B := ringKrullDim_quotient_le q
  have htop : ringKrullDim B ≠ ⊤ := (finiteRingKrullDim_iff_ne_bot_and_top.mp inferInstance).2
  rw [finiteRingKrullDim_iff_ne_bot_and_top]
  have hne : ringKrullDim (B ⧸ q) ≠ ⊥ :=
    (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞)) ringKrullDim_nonneg_of_nontrivial).ne'
  exact ⟨hne, ne_top_of_le_ne_top htop hle⟩
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
