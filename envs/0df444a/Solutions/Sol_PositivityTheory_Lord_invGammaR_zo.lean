-- Prove2me | solution 1 for PositivityTheory.Lord.invGammaR_zo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:18:39.771985+00:00
-- url     : https://prove2.me/submissions/ffe13505-db41-4aba-b373-30dcbee0f635

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_InvGammaRZo
import Theorems.Thm_PositivityTheory_Lord_invGamma_zo
import Theorems.Thm_PositivityTheory_Lord_PO_mul
import Theorems.Thm_PositivityTheory_Lord_ZO_inv
import Theorems.Thm_PositivityTheory_Lord_ZO_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex
open scoped Real
open PositivityTheory PositivityTheory.Lord
namespace PositivityTheory.Lord
theorem _root_.solution (j : ℤ) (hj : j ≤ 0) :
    ZO (fun s => (Gammaℝ s)⁻¹) (j : ℂ) (if Even j then 1 else 0) := by
  split_ifs with he
  · obtain ⟨m, hm⟩ := he
    obtain ⟨n, hn⟩ : ∃ n : ℕ, m = -(n : ℤ) := ⟨m.natAbs, by omega⟩
    obtain ⟨u, hu, hu0, hue⟩ := invGamma_zo n
    have hjn : (j : ℂ) = -(2 * (n : ℂ)) := by rw [hm, hn]; push_cast; ring
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    refine ⟨fun s => ((π : ℂ) ^ (-s / 2))⁻¹ * u (s / 2) / 2, ?_, ?_, ?_⟩
    · have h1 : AnalyticAt ℂ (fun s : ℂ => ((π : ℂ) ^ (-s / 2))⁻¹) (j : ℂ) := by
        have hd : Differentiable ℂ fun s : ℂ => (π : ℂ) ^ (-s / 2) :=
          fun s => ((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl hpi)
        exact (hd.analyticAt _).inv (by rw [Ne, cpow_eq_zero_iff]; tauto)
      have h2 : AnalyticAt ℂ (fun s : ℂ => u (s / 2)) (j : ℂ) := by
        have hc : AnalyticAt ℂ (fun s : ℂ => s / 2) (j : ℂ) := analyticAt_id.div_const
        exact hu.comp_of_eq hc (by rw [hjn]; ring)
      exact (h1.mul h2).div_const
    · simp only
      have : (j : ℂ) / 2 = -(n : ℂ) := by rw [hjn]; ring
      rw [this]
      refine div_ne_zero (mul_ne_zero (inv_ne_zero ?_) hu0) two_ne_zero
      rw [Ne, cpow_eq_zero_iff]; tauto
    · have ht : Tendsto (fun s : ℂ => s / 2) (𝓝[≠] (j : ℂ)) (𝓝[≠] (-(n : ℂ))) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have hc : Continuous fun s : ℂ => s / 2 := continuous_id.div_const 2
          have := (hc.tendsto (j : ℂ)).mono_left (nhdsWithin_le_nhds (s := {(j : ℂ)}ᶜ))
          have e : (j : ℂ) / 2 = -(n : ℂ) := by rw [hjn]; ring
          simpa only [e] using this
        · filter_upwards [self_mem_nhdsWithin] with s hs
          intro h
          apply hs
          have : s = 2 * (-(n : ℂ)) := by rw [← h]; ring
          rw [Set.mem_singleton_iff, this, hjn]; ring
      filter_upwards [ht.eventually hue] with s h1
      rw [Gammaℝ_def, mul_inv, h1, hjn]
      ring
  · have hd : Differentiable ℂ fun s => (Gammaℝ s)⁻¹ := differentiable_Gammaℝ_inv
    refine ⟨fun s => (Gammaℝ s)⁻¹, hd.analyticAt _, inv_ne_zero fun h => he ?_,
      Eventually.of_forall fun s => by simp⟩
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.1 h
    refine ⟨-(n : ℤ), ?_⟩
    have : ((j : ℤ) : ℂ) = ((-(n : ℤ) + -(n : ℤ) : ℤ) : ℂ) := by rw [hn]; push_cast; ring
    exact_mod_cast this
end PositivityTheory.Lord
