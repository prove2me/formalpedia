-- Prove2me | solution 1 for RH.Transport.nonzero_of_common_probe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:49.204094+00:00
-- url     : https://prove2.me/submissions/fd375e2a-3fbb-456f-b9d2-c0d9a7ef56da

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_Transport_Continuation
import Theorems.Thm_RH_Transport_base_lt_boundary
import Theorems.Thm_RH_Transport_common_signal_bound_at_boundary
import Theorems.Thm_OAI_SevenEighths_Continuation_gaussianMultiplier_analytic
import Theorems.Thm_OAI_SevenEighths_Continuation_gaussianMultiplier_ne_zero
import Theorems.Thm_OAI_SevenEighths_Continuation_nonzero_of_regularized_signal


set_option autoImplicit false
open RH RH.Transport
noncomputable section
open Filter Asymptotics MeasureTheory
open OAI.SevenEighths.Continuation
namespace RH.Transport
theorem _root_.solution
    (B β ω σ c : ℝ) (hω : 0 < ω)
    (L Lregular R H : ℂ → ℂ) (J f : ℝ → ℂ)
    (hL : AnalyticOnNhd ℂ Lregular {s : ℂ | B < s.re})
    (hR : AnalyticOnNhd ℂ R {s : ℂ | B < s.re})
    (hH : AnalyticOnNhd ℂ H {s : ℂ | B < s.re})
    (hcontract : ∀ s : ℂ, B < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ))
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (hzero : RapidDecayAtZero f)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (B + c + ω)))
    (herror : (fun x => J x - f x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ)))
    (heq : ∀ s : ℂ, max (continuationBoundary B β ω σ) 1 < s.re →
      Lregular s * signalMellin f c s = R s * gaussianMultiplier H s)
    {ρ : ℂ} (hρ : continuationBoundary B β ω σ < ρ.re)
    (hregular : Lregular ρ = R ρ * L ρ) (hRρ : R ρ ≠ 0) :
    L ρ ≠ 0 := by
  have hbase : B < continuationBoundary B β ω σ := base_lt_boundary hω
  have hL' : AnalyticOnNhd ℂ Lregular
      {s : ℂ | continuationBoundary B β ω σ < s.re} :=
    hL.mono (fun _ hs => hbase.trans hs)
  have hR' : AnalyticOnNhd ℂ R
      {s : ℂ | continuationBoundary B β ω σ < s.re} :=
    hR.mono (fun _ hs => hbase.trans hs)
  have hH' : AnalyticOnNhd ℂ H
      {s : ℂ | continuationBoundary B β ω σ < s.re} :=
    hH.mono (fun _ hs => hbase.trans hs)
  exact nonzero_of_regularized_signal (continuationBoundary B β ω σ) 1 c
    L Lregular R (gaussianMultiplier H) f hL' hR'
    (gaussianMultiplier_analytic hH') hlocal
    (common_signal_bound_at_boundary J f B β ω σ c hJ herror) hzero
    heq hρ hregular hRρ
    (gaussianMultiplier_ne_zero (hcontract ρ (hbase.trans hρ)))
end RH.Transport
