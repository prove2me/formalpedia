-- Prove2me | solution 1 for PI.EF.logDeriv_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:40.446526+00:00
-- url     : https://prove2.me/submissions/50544e04-625c-4a8b-90d0-eb5b97c308a9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Topology Set
namespace PI.EF
theorem _root_.solution {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hfin : analyticOrderAt f ρ ≠ ⊤) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, f s ≠ 0 ∧
      logDeriv f s = (analyticOrderNatAt f ρ : ℂ) / (s - ρ) + k s := by
  have hn : analyticOrderAt f ρ = (analyticOrderNatAt f ρ : ℕ∞) := (Nat.cast_analyticOrderNatAt hfin).symm
  obtain ⟨g, hg, hg0, hfg⟩ := (hf.analyticOrderAt_eq_natCast).1 hn
  refine ⟨fun s => deriv g s / g s, hg.deriv.div hg hg0, ?_⟩
  have hU : ∀ᶠ z in 𝓝 ρ, (∀ᶠ w in 𝓝 z, f w = (w - ρ) ^ analyticOrderNatAt f ρ • g w) ∧
      g z ≠ 0 ∧ AnalyticAt ℂ g z :=
    hfg.eventually_nhds.and ((hg.continuousAt.eventually_ne hg0).and hg.eventually_analyticAt)
  filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with s hs hsne
  obtain ⟨hfs, hgs, hga⟩ := hs
  have hsr : s - ρ ≠ 0 := sub_ne_zero.2 hsne
  have hpow : (s - ρ) ^ analyticOrderNatAt f ρ ≠ 0 := pow_ne_zero _ hsr
  have hfs' : f s = (s - ρ) ^ analyticOrderNatAt f ρ * g s := by rw [hfs.self_of_nhds, smul_eq_mul]
  refine ⟨by rw [hfs']; exact mul_ne_zero hpow hgs, ?_⟩
  have hd : DifferentiableAt ℂ (fun w : ℂ => w - ρ) s := differentiableAt_id.sub_const ρ
  have hld : logDeriv f s = logDeriv (fun w => (w - ρ) ^ analyticOrderNatAt f ρ * g w) s := by
    rw [logDeriv_apply, logDeriv_apply,
      Filter.EventuallyEq.deriv_eq (hfs.mono fun w hw => by rw [hw, smul_eq_mul]), hfs']
  have hl : logDeriv (fun w : ℂ => w - ρ) s = 1 / (s - ρ) := by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
  rw [hld, logDeriv_mul (f := fun w => (w - ρ) ^ analyticOrderNatAt f ρ) s hpow hgs (hd.pow _)
    hga.differentiableAt, logDeriv_fun_pow hd, hl, logDeriv_apply]
  beta_reduce
  ring
end PI.EF
