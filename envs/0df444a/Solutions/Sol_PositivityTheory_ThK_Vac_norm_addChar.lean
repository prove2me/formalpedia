-- Prove2me | solution 1 for PositivityTheory.ThK.Vac.norm_addChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:20:24.85002+00:00
-- url     : https://prove2.me/submissions/cac91b92-135d-4945-b286-da1e99acfd47

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_VaceigenAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.Vac
open scoped nonZeroDivisors Matrix
namespace PositivityTheory.ThK.Vac
theorem _root_.solution {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (O : Subring K)
    (hO : IsCompact (O : Set K)) (ψ : AddChar K ℂ) (hψ : Continuous ψ) (x : K) : ‖ψ x‖ = 1 := by
  have h : ∀ x : K, ‖ψ x‖ ≤ 1 := fun x => by
    obtain ⟨C, hC⟩ := hO.exists_bound_of_continuousOn (f := fun y => ψ (y * x)) (by fun_prop)
    by_contra hn
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (not_le.1 hn)
    have := hC k (natCast_mem O k)
    rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow] at this
    exact absurd hk (not_lt.2 this)
  have h1 : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
  nlinarith [h x, h (-x), norm_nonneg (ψ x), norm_nonneg (ψ (-x))]
end PositivityTheory.ThK.Vac
