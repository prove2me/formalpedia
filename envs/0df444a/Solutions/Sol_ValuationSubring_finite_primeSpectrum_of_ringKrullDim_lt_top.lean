-- Prove2me | solution 1 for ValuationSubring.finite_primeSpectrum_of_ringKrullDim_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/62866ee3-c741-5dcb-b510-bf01e7a599fd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_finite_primeSpectrum_of_ringKrullDim_lt_top

namespace AbhFinSol

open ValuationSubring

lemma finite_of_krullDim_lt_top (P : Type*) [LinearOrder P] (h : Order.krullDim P < ⊤) :
    Finite P := by
  by_contra hinf
  rw [not_finite_iff_infinite] at hinf
  have hn : ∀ n : ℕ, (n : WithBot ℕ∞) ≤ Order.krullDim P := by
    intro n
    rw [Order.le_krullDim_iff]
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq P (n + 1)
    refine ⟨⟨n, fun i => s.orderEmbOfFin hs i, fun i => ?_⟩, rfl⟩
    exact (s.orderEmbOfFin hs).strictMono (Fin.castSucc_lt_succ)
  have htop : Order.krullDim P = ⊤ := by
    have hne : Order.krullDim P ≠ ⊥ := Order.krullDim_ne_bot_iff.mpr inferInstance
    obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
    rw [← hd] at hn ⊢
    have hd' : d = ⊤ := ENat.eq_top_iff_forall_ge.mpr (fun m => by exact_mod_cast hn m)
    rw [hd']; rfl
  exact h.ne htop

end AbhFinSol

open AbhFinSol in
theorem solution {L : Type*} [Field L] (A : ValuationSubring L) (h : ringKrullDim A < ⊤) :
    Finite (PrimeSpectrum A) := by
  have e := ValuationSubring.primeSpectrumOrderEquiv A
  have hdim : Order.krullDim {S // A ≤ S} < ⊤ := by
    rw [← Order.krullDim_eq_of_orderIso e, Order.krullDim_orderDual]; exact h
  have hfin : Finite {S // A ≤ S} := finite_of_krullDim_lt_top _ hdim
  exact Finite.of_equiv _ e.toEquiv.symm

end S_ValuationSubring_finite_primeSpectrum_of_ringKrullDim_lt_top
end P2MW
export P2MW.S_ValuationSubring_finite_primeSpectrum_of_ringKrullDim_lt_top (solution)
