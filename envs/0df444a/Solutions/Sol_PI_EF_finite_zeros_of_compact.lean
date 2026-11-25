-- Prove2me | solution 1 for PI.EF.finite_zeros_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:51.481889+00:00
-- url     : https://prove2.me/submissions/b9349e1a-d9b3-46a2-9d08-16f22ef4bc22

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
theorem _root_.solution {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) : (K ∩ f ⁻¹' {0}).Finite := by
  by_contra hinf
  obtain ⟨z, _, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hK Set.inter_subset_left
  have hfr : ∃ᶠ w in 𝓝[≠] z, f w = 0 := by
    rw [accPt_iff_frequently] at hacc
    rw [Filter.Frequently, eventually_nhdsWithin_iff]
    intro h
    apply hacc
    filter_upwards [h] with w hw
    rintro ⟨hne, hw'⟩
    exact hw hne hw'.2
  have h0 := AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (fun w _ => hf.analyticAt w) isPreconnected_univ (Set.mem_univ z) hfr
  exact hx (h0 (Set.mem_univ x))
end PI.EF
