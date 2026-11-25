-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ringKrullDim_locRing_eq_of_minimalPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:48.538799+00:00
-- url     : https://prove2.me/submissions/66b81ad7-0234-43fc-8033-df9319646a81

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RingKrullDimLocRingEqOfMinimalPrime
import Theorems.Thm_ReciprocityTheory_AnForm_R_regular_point_unique_minimalPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.R
open MvPolynomial
variable {n : ℕ}
private theorem withBot_add_right_cancel {a b : WithBot ℕ∞} {c : ℕ∞} {N : ℕ}
    (h : a + (c : WithBot ℕ∞) = b + c) (hb : b + (c : WithBot ℕ∞) = N) : a = b := by
  induction b using WithBot.recBotCoe with
  | bot => simp at hb
  | coe y =>
    induction a using WithBot.recBotCoe with
    | bot => rw [← h] at hb; simp at hb
    | coe x =>
      rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_inj] at h
      rw [← WithBot.coe_add] at hb
      have hc : c ≠ ⊤ := by
        rintro rfl
        rw [add_top] at hb
        rw [← WithBot.coe_natCast, WithBot.coe_inj] at hb
        exact ENat.top_ne_natCast N hb
      exact congrArg _ (WithTop.add_right_cancel hc h)
end ReciprocityTheory.AnForm.R
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (K : Ideal (MvPolynomial (Fin n) ℂ))
    (p p' : Fin n → ℂ) [IsRegularLocalRing (locRing K p)] [IsRegularLocalRing (locRing K p')]
    (𝔮 : Ideal (MvPolynomial (Fin n) ℂ)) (h𝔮 : 𝔮 ∈ K.minimalPrimes)
    (hp : 𝔮 ≤ ptIdeal p) (hp' : 𝔮 ≤ ptIdeal p') :
    ringKrullDim (locRing K p) = ringKrullDim (locRing K p') := by
  obtain ⟨q1, -, -, hu1, hd1⟩ := regular_point_unique_minimalPrime K p
  obtain ⟨q2, -, -, hu2, hd2⟩ := regular_point_unique_minimalPrime K p'
  obtain rfl := hu1 𝔮 h𝔮 hp
  obtain rfl := hu2 𝔮 h𝔮 hp'
  rw [← hd2] at hd1
  exact withBot_add_right_cancel hd1 hd2
end ReciprocityTheory.AnForm.R
