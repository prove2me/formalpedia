-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt.lead_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:12.311908+00:00
-- url     : https://prove2.me/submissions/19b73f3a-1ca1-4247-a1ec-ac4473a4a265

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_JetsPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStartPf
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_pnorm_eq__d17dff18dae0
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_nfac_nonneg__30ef8672819a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_nfac_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_nfac_nsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_mem_multiLt_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt
theorem _root_.solution {Xa : ArchInM X} (Fl : FlatM X Xa) {δ : ℕ} (t : Fin δ → Frame X.Ψ r → ℂ) (a0 : ℕ)
    (ha0 : a0 ≤ Xa.T) (cc : (Fin (nd X) → ℕ) → Fin δ → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    {A Ct : ℝ} (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hs : ∀ q, X.pnorm Xa.L (Fl.s q) x ≤ A)
    (hw : X.pnorm Xa.L Fl.w0 x ≤ A) (ht : ∀ k, X.pnorm Xa.Fp (t k) x ≤ Ct) :
    X.pnorm (Xa.Fp + Xa.T • Xa.L) (leadM X Fl.s Fl.w0 t Xa.T a0 cc) x ≤
      (∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) a0, ∑ k, ‖cc α k‖) * Ct * A ^ Xa.T := by
  set nL := X.nfac Xa.L x with hnLdef
  set nF := X.nfac Xa.Fp x with hnFdef
  have hnL : 0 ≤ nL := nfac_nonneg' X Xa.L x
  have hnF : 0 ≤ nF := nfac_nonneg' X Xa.Fp x
  rw [pnorm_eq', nfac_add X hx, nfac_nsmul X hx]
  unfold leadM
  have hterm : ∀ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) a0, ∀ k,
      ‖cc α k * monoM X Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q) * t k x‖ * (nF * nL ^ Xa.T) ≤
        ‖cc α k‖ * Ct * A ^ Xa.T := by
    intro α hα k
    have hα' : ∑ q, α q < a0 := ReciprocityTheory.ChartRestriction.G.AR.mem_multiLt_iff.mp hα
    have hsplit : nL ^ Xa.T = (∏ q, nL ^ α q) * nL ^ (Xa.T - ∑ q, α q) := by
      rw [Finset.prod_pow_eq_pow_sum, ← pow_add, Nat.add_sub_cancel' (by omega)]
    have hAsplit : A ^ Xa.T = (∏ q, A ^ α q) * A ^ (Xa.T - ∑ q, α q) := by
      rw [Finset.prod_pow_eq_pow_sum, ← pow_add, Nat.add_sub_cancel' (by omega)]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, monoM, norm_prod, hsplit, hAsplit]
    simp only [norm_pow]
    have e : ‖cc α k‖ * (∏ q, ‖Fl.s q x‖ ^ α q) * ‖Fl.w0 x‖ ^ (Xa.T - ∑ q, α q) * ‖t k x‖ *
        (nF * ((∏ q, nL ^ α q) * nL ^ (Xa.T - ∑ q, α q))) =
        ‖cc α k‖ * (∏ q, (‖Fl.s q x‖ * nL) ^ α q) * (‖Fl.w0 x‖ * nL) ^ (Xa.T - ∑ q, α q) *
          (‖t k x‖ * nF) := by
      simp only [mul_pow, Finset.prod_mul_distrib]
      ring
    rw [e]
    have h1 : ∏ q, (‖Fl.s q x‖ * nL) ^ α q ≤ ∏ q, A ^ α q :=
      Finset.prod_le_prod (fun q _ => pow_nonneg (mul_nonneg (norm_nonneg _) hnL) _)
        (fun q _ => pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hnL) (hs q) _)
    have h2 : (‖Fl.w0 x‖ * nL) ^ (Xa.T - ∑ q, α q) ≤ A ^ (Xa.T - ∑ q, α q) :=
      pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hnL) hw _
    have h3 : ‖t k x‖ * nF ≤ Ct := ht k
    have hp1 : 0 ≤ ∏ q, (‖Fl.s q x‖ * nL) ^ α q :=
      Finset.prod_nonneg fun q _ => pow_nonneg (mul_nonneg (norm_nonneg _) hnL) _
    have hp2 : 0 ≤ (‖Fl.w0 x‖ * nL) ^ (Xa.T - ∑ q, α q) := pow_nonneg (mul_nonneg (norm_nonneg _) hnL) _
    have hA1 : 0 ≤ ∏ q, A ^ α q := Finset.prod_nonneg fun q _ => pow_nonneg hA _
    calc ‖cc α k‖ * (∏ q, (‖Fl.s q x‖ * nL) ^ α q) * (‖Fl.w0 x‖ * nL) ^ (Xa.T - ∑ q, α q) *
          (‖t k x‖ * nF)
        ≤ ‖cc α k‖ * (∏ q, A ^ α q) * A ^ (Xa.T - ∑ q, α q) * Ct := by gcongr
      _ = ‖cc α k‖ * Ct * ((∏ q, A ^ α q) * A ^ (Xa.T - ∑ q, α q)) := by ring
  have hN : 0 ≤ nF * nL ^ Xa.T := mul_nonneg hnF (pow_nonneg hnL _)
  calc ‖∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) a0, ∑ k,
        cc α k * monoM X Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q) * t k x‖ * (nF * nL ^ Xa.T)
      ≤ (∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) a0, ∑ k,
          ‖cc α k * monoM X Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q) * t k x‖) * (nF * nL ^ Xa.T) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => norm_sum_le _ _)
    _ = ∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) a0, ∑ k,
          ‖cc α k * monoM X Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q) * t k x‖ * (nF * nL ^ Xa.T) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun α _ => Finset.sum_mul _ _ _
    _ ≤ ∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) a0, ∑ k, ‖cc α k‖ * Ct * A ^ Xa.T :=
        Finset.sum_le_sum fun α hα => Finset.sum_le_sum fun k _ => hterm α hα k
    _ = _ := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun α _ => by rw [Finset.sum_mul, Finset.sum_mul]
end ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt
