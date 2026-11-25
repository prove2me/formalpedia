-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds.rho_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:36:45.876519+00:00
-- url     : https://prove2.me/submissions/8eb7a89a-47f0-40c9-9002-3082d2b49bdb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FjFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CuspStatementPf
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_dmin_flow__e85f3e11be45

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
  ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
noncomputable section
open ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)
variable (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
  (s : X.Ψ → ℂ) (hT : X.flowV e s x ∈ X.dom) (τ : X.Ψ)
include he hx
include hT
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds
theorem _root_.solution : ∀ i ≤ r, 0 < rho X e s x τ i := fun i hi => by
  have h1 := (hT τ).2 ⟨i, Nat.lt_succ_of_le hi⟩
  rw [dmin_flow' X e he hx s τ, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, ← mul_assoc] at h1
  exact (mul_pos_iff_of_pos_left ((hx τ).2 ⟨i, Nat.lt_succ_of_le hi⟩)).mp h1
end ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds
