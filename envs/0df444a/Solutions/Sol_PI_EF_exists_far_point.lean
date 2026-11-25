-- Prove2me | solution 1 for PI.EF.exists_far_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:35.066425+00:00
-- url     : https://prove2.me/submissions/f2cb8a4e-9d9f-49cd-a4eb-9a485b455232

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open DirichletCharacter
namespace PI.EF
theorem _root_.solution (S : Finset ℝ) (a : ℝ) :
    ∃ x ∈ Set.Icc a (a + 1), ∀ y ∈ S, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |x - y| := by
  by_contra hcon
  push_neg at hcon
  have hK : (0 : ℝ) < (S.card : ℝ) + 1 := by positivity
  have hpt : ∀ i ∈ Finset.range (S.card + 2), a + (i : ℝ) / ((S.card : ℝ) + 1) ∈ Set.Icc a (a + 1) := by
    intro i hi
    have hi' : (i : ℝ) ≤ (S.card : ℝ) + 1 := by
      have := Finset.mem_range.1 hi
      exact_mod_cast Nat.lt_succ_iff.1 this
    constructor
    · have : 0 ≤ (i : ℝ) / ((S.card : ℝ) + 1) := by positivity
      linarith
    · have : (i : ℝ) / ((S.card : ℝ) + 1) ≤ 1 := (div_le_one hK).2 hi'
      linarith
  have hex : ∀ i ∈ Finset.range (S.card + 2), ∃ y ∈ S,
      |a + (i : ℝ) / ((S.card : ℝ) + 1) - y| < 1 / (2 * ((S.card : ℝ) + 1)) :=
    fun i hi => hcon _ (hpt i hi)
  choose! g hgS hgd using hex
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (S.card + 2)) (t := S) (by simp) (fun i hi => hgS i hi)
  have h1 := hgd i hi
  have h2 := hgd j hj
  rw [heq] at h1
  have hlt : |(a + (i : ℝ) / ((S.card : ℝ) + 1)) - (a + (j : ℝ) / ((S.card : ℝ) + 1))| <
      1 / ((S.card : ℝ) + 1) := by
    have htri := abs_sub_le (a + (i : ℝ) / ((S.card : ℝ) + 1)) (g j) (a + (j : ℝ) / ((S.card : ℝ) + 1))
    rw [abs_sub_comm (g j)] at htri
    have e : 1 / (2 * ((S.card : ℝ) + 1)) + 1 / (2 * ((S.card : ℝ) + 1)) = 1 / ((S.card : ℝ) + 1) := by
      field_simp
      ring
    linarith
  have hge : 1 / ((S.card : ℝ) + 1) ≤
      |(a + (i : ℝ) / ((S.card : ℝ) + 1)) - (a + (j : ℝ) / ((S.card : ℝ) + 1))| := by
    rw [show (a + (i : ℝ) / ((S.card : ℝ) + 1)) - (a + (j : ℝ) / ((S.card : ℝ) + 1)) =
      ((i : ℝ) - j) / ((S.card : ℝ) + 1) by ring, abs_div, abs_of_pos hK]
    apply div_le_div_of_nonneg_right _ hK.le
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      exact le_abs.2 (Or.inr (by linarith))
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      exact le_abs.2 (Or.inl (by linarith))
  linarith
end PI.EF
