-- Prove2me | solution 1 for PositivityTheory.CW.second_derivative_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:33:07.991636+00:00
-- url     : https://prove2.me/submissions/ce7f250b-c315-4759-bb81-5185922b10bf

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CompactGroupFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS Filter Topology Set
open PositivityTheory PositivityTheory.CW
namespace PositivityTheory.CW
theorem _root_.solution : B3 := by
  intro ψ ψ' d hmax hψ hd
  by_contra hneg
  have hdpos : 0 < d := lt_of_not_ge hneg
  have h0 : ψ' 0 = 0 := hmax.hasDerivAt_eq_zero (hψ 0)
  have hslope := hd.tendsto_slope_zero_right
  have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ψ t ≤ ψ 0 := nhdsWithin_le_nhds hmax
  have e2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (ψ' (0 + t) - ψ' 0) := hslope (lt_mem_nhds hdpos)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (e1.and e2)
  have hu0 : (0 : ℝ) < u := hu
  have hb : u / 2 ∈ Set.Ioo (0 : ℝ) u := ⟨by linarith, by linarith⟩
  obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope ψ ψ' (half_pos hu0)
    (fun t _ => (hψ t).continuousAt.continuousWithinAt) (fun t _ => hψ t)
  have hcu : c ∈ Set.Ioo (0 : ℝ) u := ⟨hc.1, hc.2.trans (by linarith)⟩
  obtain ⟨-, hc'⟩ := hsub hcu
  obtain ⟨hbmax, -⟩ := hsub hb
  simp only [zero_add, h0, sub_zero, smul_eq_mul] at hc'
  have hψc : 0 < ψ' c := (pos_iff_pos_of_mul_pos hc').mp (inv_pos.mpr hc.1)
  rw [hcslope, sub_zero] at hψc
  have hdiff : 0 < ψ (u / 2) - ψ 0 := by
    have := mul_pos hψc (half_pos hu0)
    rwa [div_mul_cancel₀ _ (half_pos hu0).ne'] at this
  linarith
end PositivityTheory.CW
