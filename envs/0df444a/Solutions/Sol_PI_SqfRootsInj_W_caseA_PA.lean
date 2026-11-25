-- Prove2me | solution 1 for PI.SqfRootsInj.W.caseA_PA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:27:08.421583+00:00
-- url     : https://prove2.me/submissions/2581e2b7-6971-4708-8019-13fe533b2d41

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
    (hB : ℓ ∉ BB r g) (h : CaseA g r ℓ f) : PA g r f := by
  have hg2 : 1 < g := hg.out.one_lt
  obtain ⟨e, j, w, he2, her, hj1, hj2, hdv, hdeg, hdvd, hpow⟩ := h
  refine ⟨e, ?_, j, ?_, ℓ, ?_, w, ?_, hdvd⟩
  · exact Finset.mem_Icc.2 ⟨he2, her⟩
  · exact Finset.mem_Icc.2 ⟨hj1, by omega⟩
  · exact Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hℓ, hdv, g_pow_sub_one_ne hg2 (by omega)⟩, hB⟩
  · refine Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 ((mem_nthRoots ?_).2 hpow), hdeg⟩
    have : 1 ≤ g ^ j - 1 := by
      have := Nat.one_lt_pow (by omega : j ≠ 0) hg2
      omega
    exact Nat.mul_pos this (lp_pos hℓ)
end PI.SqfRootsInj.W
