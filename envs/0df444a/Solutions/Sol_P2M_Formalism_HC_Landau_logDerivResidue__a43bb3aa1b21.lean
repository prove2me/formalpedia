-- Prove2me | solution 1 for P2M_Formalism_HC_Landau_logDerivResidue__a43bb3aa1b21
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:30:08.767809+00:00
-- url     : https://prove2.me/submissions/289acef5-a6a8-4432-a633-f67d80d6a0ce

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_landauIteratedDerivatives_key
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism Formalism.HC Formalism.HC.Landau
open Formalism ArithmeticFunction
namespace Formalism.HC.Landau
theorem _root_.solution : LogDerivResidue := by
  intro f ρ hf ⟨z, hz⟩
  have hfa : ∀ w, AnalyticAt ℂ f w := fun w => hf.analyticAt w
  have hne : analyticOrderAt f ρ ≠ ⊤ := by
    rw [Ne, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ hfa]
    intro h
    exact hz (by simp [h])
  set m := analyticOrderNatAt f ρ with hm
  obtain ⟨g, hga, hgρ, hfg⟩ := ((hfa ρ).analyticOrderNatAt_eq_iff hne (n := m)).mp rfl
  have hfg' : f =ᶠ[𝓝 ρ] fun s => (s - ρ) ^ m * g s := by
    filter_upwards [hfg] with s hs
    simpa using hs
  have hderiv : deriv f =ᶠ[𝓝 ρ] deriv (fun s => (s - ρ) ^ m * g s) := hfg'.deriv
  have hgan : ∀ᶠ s in 𝓝 ρ, AnalyticAt ℂ g s := hga.eventually_analyticAt
  have hgne : ∀ᶠ s in 𝓝 ρ, g s ≠ 0 := hga.continuousAt.eventually_ne hgρ
  have key : (fun s => (m : ℂ) + (s - ρ) * (deriv g s / g s)) =ᶠ[𝓝[≠] ρ]
      fun s => (s - ρ) * (deriv f s / f s) := by
    have h1 : ∀ᶠ s in 𝓝[≠] ρ, s ≠ ρ := self_mem_nhdsWithin
    filter_upwards [nhdsWithin_le_nhds hfg', nhdsWithin_le_nhds hderiv,
      nhdsWithin_le_nhds hgan, nhdsWithin_le_nhds hgne, h1] with s hfs hds hgs hgs0 hsρ
    have hsub : s - ρ ≠ 0 := sub_ne_zero.mpr hsρ
    have hd : deriv (fun s => (s - ρ) ^ m * g s) s =
        (m : ℂ) * (s - ρ) ^ (m - 1) * g s + (s - ρ) ^ m * deriv g s := by
      have h2 : HasDerivAt (fun s => (s - ρ) ^ m) ((m : ℂ) * (s - ρ) ^ (m - 1)) s := by
        simpa using ((hasDerivAt_id s).sub_const ρ).fun_pow m
      exact (h2.mul hgs.differentiableAt.hasDerivAt).deriv
    rw [hds, hfs, hd]
    have hpow : (s - ρ) * (s - ρ) ^ (m - 1) * (m : ℂ) = (m : ℂ) * (s - ρ) ^ m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · simp [h0]
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        rw [hk]; simp [pow_succ]; ring
    have hpm : (s - ρ) ^ m ≠ 0 := pow_ne_zero _ hsub
    field_simp
    linear_combination (-(g s)) * hpow
  refine Tendsto.congr' key ?_
  have hdg : ContinuousAt (deriv g) ρ := hga.deriv.continuousAt
  have hlim : Tendsto (fun s => (m : ℂ) + (s - ρ) * (deriv g s / g s)) (𝓝 ρ)
      (𝓝 ((m : ℂ) + (ρ - ρ) * (deriv g ρ / g ρ))) := by
    refine tendsto_const_nhds.add ?_
    exact ((continuous_id.sub continuous_const).continuousAt.tendsto).mul
      (hdg.tendsto.div hga.continuousAt.tendsto hgρ)
  simpa using hlim.mono_left nhdsWithin_le_nhds
end Formalism.HC.Landau
