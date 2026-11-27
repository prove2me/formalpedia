-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.exists_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:27.765884+00:00
-- url     : https://prove2.me/submissions/f986352d-0d7d-4fa0-a6af-02de90a88436

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_constantCoeff_prim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_prim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [Fintype τ] [DecidableEq τ]
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution (ω : τ → MvPowerSeries τ k) (hω : ∀ a c, pderiv k c (ω a) = pderiv k a (ω c)) :
    ∃ ℓ : MvPowerSeries τ k, constantCoeff ℓ = 0 ∧ ∀ v, pderiv k v ℓ = ω v :=
  ⟨prim ω, constantCoeff_prim ω, pderiv_prim ω hω⟩
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
