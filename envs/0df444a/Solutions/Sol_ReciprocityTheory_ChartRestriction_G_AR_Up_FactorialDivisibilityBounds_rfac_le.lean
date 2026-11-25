-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds.rfac_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:10:22.540203+00:00
-- url     : https://prove2.me/submissions/1e37c22e-0ceb-4ce5-8fd1-c8f8ed753ac1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FjFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CuspStatementPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_abel_bound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_rho_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_rfac_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_hG_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_hsg_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_maj_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_bounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



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
theorem _root_.solution (la : Wt X.Ψ r) (hs : 0 ≤ (s τ).im) (hp0 : 0 < X.p0) (hp0r : X.p0 < r)
    (hgap : ∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → la τ j ≤ la τ i)
    (hpair : ∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → la τ i0 < la τ i1) :
    rfac X la x (X.flowV e s x) τ ≤
      Real.exp (-(1 / 2) * Real.log (1 + (s τ).im / X.ttV e x τ)) := by
  rw [rfac_eq X e he hx s hT τ la]
  apply Real.exp_le_exp.mpr
  have hρ := rho_pos X e he hx s hT τ
  have hsg := hsg_of X hx τ
  have hb : 0 ≤ 2 * X.c τ * (s τ).im := by have := c_pos X τ; positivity
  have hmb : ∀ i ≤ r, 0 ≤ mN τ.1 X.Gm (mat x τ) (e τ) i ∧
      mN τ.1 X.Gm (mat x τ) (e τ) i ≤ mN τ.1 X.Gm (mat x τ) (e τ) X.p0 :=
    fun i hi => mN_bounds (hG_of X τ) X.p0 X.p0_le (mat x τ) (hx τ).1 hsg (e τ) (he τ).1 i hi
  set L : ℕ → ℝ := fun i => Real.log (rho X e s x τ i) with hLdef
  have hL0 : L 0 = 0 := by simp [L, rho, mN_zero]
  have hLr : L r = 0 := by
    simp [L, rho, mN_top (hG_of X τ) X.p0 (mat x τ) (hx τ).1 hsg (e τ) (he τ).1]
  have hLle : ∀ k ≤ r, L k ≤ L X.p0 := fun k hk => by
    apply Real.log_le_log (hρ k hk)
    simp only [rho]
    nlinarith [(hmb k hk).2]
  have hLp : 0 ≤ L X.p0 := by
    apply Real.log_nonneg
    simp only [rho]
    nlinarith [(hmb X.p0 X.p0_le).1]
  set a : ℕ → ℝ := fun k => if h : k < r then (la τ ⟨k, h⟩ : ℝ) / 2 else 0 with ha
  have hsum : ∑ i : Fin r, (la τ i : ℝ) / 2 *
      (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i)) =
      ∑ k ∈ Finset.range r, a k * (L (k + 1) - L k) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => a k * (L (k + 1) - L k)) r]
    exact Finset.sum_congr rfl fun i _ => by simp only [a, L, dif_pos i.2]
  have hgap' : ∀ k, 1 ≤ k → k < r → k ≠ X.p0 → a k ≤ a (k - 1) := by
    intro k hk1 hkr hkp
    simp only [a, dif_pos hkr, dif_pos (show k - 1 < r by omega)]
    have := hgap ⟨k - 1, by omega⟩ ⟨k, hkr⟩ (by simp; omega) hkp
    have : (la τ ⟨k, hkr⟩ : ℝ) ≤ la τ ⟨k - 1, by omega⟩ := by exact_mod_cast this
    linarith
  have hab := abel_bound a L X.p0 r hLle hgap' r (by omega) le_rfl
  rw [hL0, hLr] at hab
  have hpa : a 0 - a (r - 1) ≤ -(1 / 2) := by
    simp only [a, dif_pos (show 0 < r by omega), dif_pos (show r - 1 < r by omega)]
    have := hpair ⟨0, by omega⟩ ⟨r - 1, by omega⟩ rfl rfl
    have : (la τ ⟨0, by omega⟩ : ℝ) + 1 ≤ la τ ⟨r - 1, by omega⟩ := by exact_mod_cast this
    linarith
  have hq : 1 + (s τ).im / X.ttV e x τ = rho X e s x τ X.p0 := by
    rw [Data.ttV, maj_eq X hx e τ (he τ).1, div_div_eq_mul_div, div_one]
    simp only [rho]
    ring
  rw [hsum, hq]
  have : (a 0 - a (r - 1)) * L X.p0 ≤ -(1 / 2) * L X.p0 :=
    mul_le_mul_of_nonneg_right hpa hLp
  show _ ≤ -(1 / 2) * L X.p0
  linarith
end ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds
