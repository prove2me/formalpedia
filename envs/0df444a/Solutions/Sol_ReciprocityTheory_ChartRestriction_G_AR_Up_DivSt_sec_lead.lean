-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt.sec_lead
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:09:27.18945+00:00
-- url     : https://prove2.me/submissions/30bf105f-c3e5-4a9d-b689-86606e5489ec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_JetsPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStartPf
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_sec_mul__4b7051dfc546
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_sec_cmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_sec_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_sec_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_sec_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_mem_multiLt_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
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
theorem _root_.solution {Xa : ArchInM X} (Fl : FlatM X Xa) {δ : ℕ} (t : Fin δ → Frame X.Ψ r → ℂ)
    (ht : ∀ k, X.IsSec Xa.Fp (t k)) (hs : ∀ k, X.IsSec Xa.L (Fl.s k)) (hw : X.IsSec Xa.L Fl.w0)
    (a0 : ℕ) (ha0 : a0 ≤ Xa.T) (cc : (Fin (nd X) → ℕ) → Fin δ → ℂ) :
    X.IsSec (Xa.Fp + Xa.T • Xa.L) (leadM X Fl.s Fl.w0 t Xa.T a0 cc) := by
  unfold leadM
  refine sec_sum X _ fun α hα => sec_sum X _ fun k _ => ?_
  have hα' : ∑ q, α q < a0 := ReciprocityTheory.ChartRestriction.G.AR.mem_multiLt_iff.mp hα
  have hm : X.IsSec ((∑ q, α q) • Xa.L) (monoM X Fl.s α) := by
    have := sec_prod X Finset.univ (fun q => α q • Xa.L) (P := fun q x => Fl.s q x ^ α q)
      (fun q _ => sec_pow X (hs q) (α q))
    rw [← Finset.sum_smul] at this
    exact this
  have h1 := sec_mul' X (sec_mul' X hm (sec_pow X hw (Xa.T - ∑ q, α q))) (ht k)
  have hwt : (∑ q, α q) • Xa.L + (Xa.T - ∑ q, α q) • Xa.L + Xa.Fp = Xa.Fp + Xa.T • Xa.L := by
    rw [← add_smul, Nat.add_sub_cancel' (by omega), add_comm]
  rw [hwt] at h1
  have h2 := sec_cmul X (cc α k) h1
  refine ⟨h2.1.congr fun x _ => by simp [mul_assoc], fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have := h2.2.1 x hx b hb; simp only [mul_assoc] at this ⊢; exact this
  · have := h2.2.2 γ hγ x hx; simp only [mul_assoc] at this ⊢; exact this
end ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt
