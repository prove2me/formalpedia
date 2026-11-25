-- Prove2me | solution 1 for PositivityTheory.ThK.SiegelT.norm_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:05.095702+00:00
-- url     : https://prove2.me/submissions/5fb94370-ec1d-4cbe-9c16-16236fb3ed48

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM Topology Filter
namespace PositivityTheory.ThK.SiegelT
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ψ : AddChar k ℂ}
    (hψ : Continuous ψ) (x : k) : ‖ψ x‖ = 1 := by
  have hle : ∀ y : k, ‖ψ y‖ ≤ 1 := fun y => by
    by_contra hlt
    push Not at hlt
    obtain ⟨B, hB⟩ := (IsNonarchimedeanLocalField.isCompact_closedBall k (ValuativeRel.valuation k y)).exists_bound_of_continuousOn
      hψ.continuousOn
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hlt
    have := hB (n • y) (by
      rw [Set.mem_ofPred_eq, nsmul_eq_mul, map_mul]
      exact mul_le_of_le_one_left' (natCast_mem (ValuativeRel.valuation k).integer n))
    rw [AddChar.map_nsmul_eq_pow, norm_pow] at this
    exact absurd hn (not_lt.mpr this)
  have h1 : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
  refine le_antisymm (hle x) ?_
  nlinarith [hle x, hle (-x), norm_nonneg (ψ x), norm_nonneg (ψ (-x))]
end PositivityTheory.ThK.SiegelT
