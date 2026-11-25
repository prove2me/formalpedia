-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.av_no_two_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:29:43.667502+00:00
-- url     : https://prove2.me/submissions/c6596922-d773-4222-bd11-9f2d9f4035fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AvPrimeDimOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {S : Type*} [CommRing S] [IsDomain S] {A B : Ideal S} [A.IsPrime]
    [B.IsPrime] (h1 : ⊥ < A) (h2 : A < B) (hB : B.height ≤ 1) : False := by
  have hza : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum S) < ⟨A, ‹A.IsPrime›⟩ := h1
  have hab : (⟨A, ‹A.IsPrime›⟩ : PrimeSpectrum S) < ⟨B, ‹B.IsPrime›⟩ := h2
  have e1 := Order.height_add_one_le hza
  have e2 := Order.height_add_one_le hab
  unfold Ideal.height at hB
  refine absurd hB (not_le.mpr (lt_of_lt_of_le (show (1 : ℕ∞) < 2 by norm_num)
    (le_iInf₂ fun J hJ => ?_)))
  have hJB : J = B := by
    have h' := hJ
    rw [Ideal.minimalPrimes_eq_subsingleton_self] at h'
    exact h'
  subst hJB
  change (2 : ℕ∞) ≤ Order.height (⟨J, ‹J.IsPrime›⟩ : PrimeSpectrum S)
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ _ := le_trans (add_le_add (le_add_self.trans e1) le_rfl) e2
end ReciprocityTheory.ChartRestriction.G.T0
