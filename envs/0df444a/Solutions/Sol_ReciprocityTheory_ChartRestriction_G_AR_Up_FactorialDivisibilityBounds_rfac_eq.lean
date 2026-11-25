-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds.rfac_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:00:31.1292+00:00
-- url     : https://prove2.me/submissions/39b2e853-b9e7-425e-85b2-6c990ffda826

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FjFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CuspStatementPf
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_dmin_flow__e85f3e11be45
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_dmin_ne__f45090e2d31f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_rho_pos

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
theorem _root_.solution (la : Wt X.Ψ r) :
    rfac X la x (X.flowV e s x) τ = Real.exp (∑ i : Fin r, (la τ i : ℝ) / 2 *
      (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i))) := by
  have hρ := rho_pos X e he hx s hT τ
  have hfac : ∀ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) /
      ‖dmin X.Gm (X.flowV e s x) τ i.succ / dmin X.Gm (X.flowV e s x) τ i.castSucc‖ ^
        (-(la τ i : ℝ) / 2) =
      Real.exp ((la τ i : ℝ) / 2 *
        (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i))) := by
    intro i
    have hρ1 := hρ ((i : ℕ) + 1) i.2
    have hρ0 := hρ i i.2.le
    have hN : 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
      norm_pos_iff.mpr (div_ne_zero (dmin_ne' X e he hx τ _) (dmin_ne' X e he hx τ _))
    rw [dmin_flow' X e he hx s τ, dmin_flow' X e he hx s τ, Fin.val_succ, Fin.val_castSucc]
    have hn : ‖dmin X.Gm x τ i.succ * ((rho X e s x τ ((i : ℕ) + 1) : ℝ) : ℂ) /
        (dmin X.Gm x τ i.castSucc * ((rho X e s x τ i : ℝ) : ℂ))‖ =
        ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ *
          (rho X e s x τ ((i : ℕ) + 1) / rho X e s x τ i) := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hρ1.le, Real.norm_of_nonneg hρ0.le, norm_div]
      field_simp
    rw [hn, Real.mul_rpow hN.le (div_pos hρ1 hρ0).le,
      div_mul_cancel_left₀ (Real.rpow_pos_of_pos hN _).ne', ← Real.rpow_neg (div_pos hρ1 hρ0).le,
      Real.rpow_def_of_pos (div_pos hρ1 hρ0), Real.log_div hρ1.ne' hρ0.ne']
    congr 1
    ring
  rw [rfac, Finset.prod_congr rfl fun i _ => hfac i, ← Real.exp_sum]
end ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds
