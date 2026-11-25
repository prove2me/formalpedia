-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IntegerToRational.length_le_coheight_eQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:24:29.151436+00:00
-- url     : https://prove2.me/submissions/fd9be8a4-49d3-490b-9c49-2366de10967e

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatB
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_eQ_lt
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_dim_le_of_charP
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_map_isPrime
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_ringKrullDim_quotient_eq_coheight


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IntegerToRational
open MvPolynomial
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R.IntegerToRational
theorem _root_.solution (s : LTSeries (PrimeSpectrum (MvPolynomial σ ℤ))) :
    ∀ z, s.head = z → ∀ h0 : ChZero z.asIdeal,
      (s.length : ℕ∞) ≤ Order.coheight (eQ z h0) + 1 := by
  induction s using RelSeries.inductionOn with
  | singleton x => intros; simp
  | cons t x hx ih =>
    intro z hz h0
    rw [RelSeries.head_cons] at hz
    subst hz
    simp only [RelSeries.cons_length, Nat.cast_add, Nat.cast_one]
    by_cases h1 : ChZero t.head.asIdeal
    · have h2 := ih t.head rfl h1
      have h3 := Order.coheight_add_one_le (eQ_lt h0 h1 hx)
      calc (t.length : ℕ∞) + 1 ≤ Order.coheight (eQ t.head h1) + 1 + 1 := add_le_add_left h2 1
        _ ≤ Order.coheight (eQ x h0) + 1 := add_le_add_left h3 1
    · have h2 : (t.length : ℕ∞) ≤ Order.coheight t.head := Order.length_le_coheight_head
      have h3 := dim_le_of_charP x.asIdeal t.head.asIdeal hx.le h0 h1
      rw [ringKrullDim_quotient_eq_coheight,
        ringKrullDim_quotient_eq_coheight (hI := map_isPrime _ h0)] at h3
      have h4 : Order.coheight t.head ≤ Order.coheight (eQ x h0) := WithBot.coe_le_coe.mp h3
      calc (t.length : ℕ∞) + 1 ≤ Order.coheight t.head + 1 := add_le_add_left h2 1
        _ ≤ Order.coheight (eQ x h0) + 1 := add_le_add_left h4 1
end ReciprocityTheory.AnForm.R.IntegerToRational
