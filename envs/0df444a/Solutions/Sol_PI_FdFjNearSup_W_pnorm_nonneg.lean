-- Prove2me | solution 1 for PI.FdFjNearSup.W.pnorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:22.512815+00:00
-- url     : https://prove2.me/submissions/19765ab5-f375-4094-b8a3-8f9552686fee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_FdFjNearSupOf
import Theorems.Thm_PI_FdFjNearSup_W_nfac_pos
import Theorems.Thm_PI_FdFjNearSup_W_pnorm_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FdFjNearSup PI.FdFjNearSup.W
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex MeasureTheory
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace PI.FdFjNearSup.W
theorem _root_.solution {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : 0 ≤ X.pnorm la Q x := by
  rw [pnorm_eq]
  exact mul_nonneg (norm_nonneg _) (nfac_pos X la hx).le
end PI.FdFjNearSup.W
