-- Prove2me | solution 1 for PI.SqfRootsInj.W.caseB_PB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:25:44.305799+00:00
-- url     : https://prove2.me/submissions/d5a4f099-569b-4c5e-ab93-a40beb6b98e7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_DivCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_TwoPowCardPrimeFactorsLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover
import Theorems.Thm_PI_SqfRootsInj_W_lp_pos
import Theorems.Thm_PI_SqfRootsInj_W_g_pow_sub_one_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution {g r ℓ : ℕ} [hg : Fact g.Prime] {f : (ZMod g)[X]} (hℓ : ℓ.Prime)
    (hB : ℓ ∉ BB r g) (h : CaseB g r ℓ f) : PB g r f := by
  have hg2 : 1 < g := hg.out.one_lt
  obtain ⟨e, e', x, y, he', he'e, hsum, hdv, hdx, hdy, hdvd, hy, hx⟩ := h
  refine ⟨e, ?_, e', ?_, ℓ, ?_, y, ?_, x, ?_, hdvd⟩
  · exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · exact Finset.mem_Icc.2 ⟨he', by omega⟩
  · exact Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2
      ⟨hℓ, hdv, Nat.mul_ne_zero (g_pow_sub_one_ne hg2 (by omega)) (g_pow_sub_one_ne hg2 he')⟩, hB⟩
  · refine Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 ?_, hdy⟩
    have hM : 1 < g ^ e' := Nat.one_lt_pow (by omega) hg2
    rw [mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ hM)]
    simp [hy]
  · exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 ((mem_nthRoots (lp_pos hℓ)).2 hx), hdx⟩
end PI.SqfRootsInj.W
