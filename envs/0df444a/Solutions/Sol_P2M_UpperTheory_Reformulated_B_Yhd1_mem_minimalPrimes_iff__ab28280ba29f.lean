-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Yhd1_mem_minimalPrimes_iff__ab28280ba29f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:29.624372+00:00
-- url     : https://prove2.me/submissions/69351702-b702-42f6-b8d1-21510d995b42

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemMinimalPrimesIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Yhd1.mem_minimalPrimes_iff
theorem _root_.solution.{u_1} :
    ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A] [IsNoetherianRing A] {z : A},
      z ≠ (0 : A) → ∀ (W : Ideal A), W ∈ (Ideal.span {z}).minimalPrimes ↔ W.IsPrime ∧ W.height = (1 : ℕ∞) ∧ z ∈ W := by
  intro A _ _ _ z hz
  have key : ∀ P : Ideal A, P.IsPrime → z ∈ P → (1 : ℕ∞) ≤ P.height := by
    intro P hP hzP
    have hlt : (⊥ : Ideal A) < P := by
      refine bot_lt_iff_ne_bot.mpr fun h => hz ?_
      rw [h] at hzP
      exact Ideal.mem_bot.mp hzP
    have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    exact le_trans le_add_self this
  intro W
  constructor
  · intro hW
    have hP : W.IsPrime := hW.1.1
    have hzW : z ∈ W := hW.1.2 (Ideal.mem_span_singleton_self z)
    exact ⟨hP, le_antisymm
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hW) (key W hP hzW), hzW⟩
  · rintro ⟨hP, hh, hzW⟩
    obtain ⟨P, hPm, hPW⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem W).mpr hzW)
    have hP' : P.IsPrime := hPm.1.1
    have hzP : z ∈ P := hPm.1.2 (Ideal.mem_span_singleton_self z)
    rcases hPW.eq_or_lt with h | h
    · exact h ▸ hPm
    · exfalso
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime h
      have h2 : (1 : ℕ∞) + 1 ≤ 1 := by
        calc (1 : ℕ∞) + 1 ≤ P.height + 1 := by gcongr; exact key P hP' hzP
          _ ≤ W.height := h1
          _ = 1 := hh
      exact absurd h2 (by decide)
end UpperTheory.Reformulated.B.Yhd1.mem_minimalPrimes_iff
