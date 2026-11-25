-- Prove2me | solution 1 for PI.FdFjNearSup.W.spread_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:02.751343+00:00
-- url     : https://prove2.me/submissions/d0a2c453-0248-4ec7-8ad9-f5c0abe06bce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_FdFjNearSupOf

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
theorem _root_.solution {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (τ : X.Ψ) : 0 ≤ X.spread la τ := by
  unfold Data.spread
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp
  · have hb := Set.finite_range (fun i : Fin r => (la τ i : ℝ))
    exact sub_nonneg.2 ((ciInf_le hb.bddBelow (⟨0, hr⟩ : Fin r)).trans
      (le_ciSup hb.bddAbove (⟨0, hr⟩ : Fin r)))
end PI.FdFjNearSup.W
