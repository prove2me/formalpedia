-- Prove2me | solution 1 for PI.FdFjNearSup.W.dmin_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:55.136124+00:00
-- url     : https://prove2.me/submissions/1d8c0e3a-7601-4c9c-8690-6621aafa9956

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
theorem _root_.solution {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ)
    (j : Fin (r + 1)) : dmin X.Gm x τ j ≠ 0 := by
  intro h0
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx
  have h1 := (hx τ).2 j
  rw [h0, Complex.zero_re, mul_zero] at h1
  exact lt_irrefl _ h1
end PI.FdFjNearSup.W
