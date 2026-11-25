-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_prod_one_sub_eq_zero_efeffefc5a98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:53:05.396257+00:00
-- url     : https://prove2.me/submissions/65059bcd-25db-4355-90a7-97f9f3872133

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.RestTerms.Schur
theorem _root_.solution {ι : Type*} [DecidableEq ι] (a : ι → R) (s : Finset ι) :
    ∀ c : ℕ, s.card < c →
      PowerSeries.coeff c (∏ i ∈ s, (1 - PowerSeries.C (a i) * PowerSeries.X)) = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro c hc
    simp only [prod_empty, PowerSeries.coeff_one]
    simp at hc; simp [Nat.pos_iff_ne_zero.mp hc]
  | insert j s hj ih =>
    intro c hc
    rw [card_insert_of_notMem hj] at hc
    rw [prod_insert hj, sub_mul, one_mul, map_sub, ih c (by omega)]
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [mul_assoc, mul_comm PowerSeries.X, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X,
      ih c (by omega)]
    simp
end GroundTheory.Heights₂.Heights.RestTerms.Schur
