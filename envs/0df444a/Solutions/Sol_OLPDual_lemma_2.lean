-- Prove2me | solution 1 for OLPDual.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:11:58.5612+00:00
-- url     : https://prove2.me/submissions/715e9511-6513-49f0-8593-c09f00724582

import Mathlib
import Definitions.Def_OLPDual_Model

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OLPDual.Aux_OD

theorem antitone_ind (r : ℝ) : Antitone fun v : ℝ => if r > v then (1 : ℝ) else 0 := by
  intro a b hab
  simp only
  split_ifs with h1 h2 h2 <;> first | (exfalso; linarith) | norm_num

theorem integral_ind (r x y : ℝ) :
    ∫ v in x..y, (if r > v then (1 : ℝ) else 0) = min y r - min x r := by
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right
  · exact (continuous_id.min continuous_const).continuousOn
  · intro v _
    by_cases hv : v < r
    · rw [if_pos hv]
      have h1 : HasDerivWithinAt (fun u : ℝ => u) 1 (Set.Ioi v) v :=
        (hasDerivAt_id' v).hasDerivWithinAt
      apply h1.congr_of_eventuallyEq
      · filter_upwards [Ioo_mem_nhdsGT hv] with w hw
        exact min_eq_left hw.2.le
      · exact min_eq_left hv.le
    · push_neg at hv
      rw [if_neg (not_lt.mpr hv)]
      have h1 : HasDerivWithinAt (fun _ : ℝ => r) 0 (Set.Ioi v) v := hasDerivWithinAt_const _ _ _
      apply h1.congr
      · intro w hw
        exact min_eq_right (le_of_lt (lt_of_le_of_lt hv hw))
      · exact min_eq_right hv
  · exact (antitone_ind r).intervalIntegrable

end OLPDual.Aux_OD

open OLPDual OLPDual.Aux_OD in
theorem solution {m n : ℕ} (hn : 0 < n) (d : E m) (ω : Sample m n) (p pstar : E m) :
    fn d ω p - fn d ω pstar =
      (1 / (n : ℝ)) * ∑ j, ⟪phi d pstar (ω j), p - pstar⟫ +
        (1 / (n : ℝ)) * ∑ j, knightTerm (ω j).1 (ω j).2 p pstar := by
  have hK : ∀ (a : E m) (r : ℝ), knightTerm a r p pstar =
      (min ⟪a, pstar⟫ r - min ⟪a, p⟫ r) -
        (if r > ⟪a, pstar⟫ then (1 : ℝ) else 0) * (⟪a, pstar⟫ - ⟪a, p⟫) := by
    intro a r
    unfold knightTerm
    rw [intervalIntegral.integral_sub (antitone_ind r).intervalIntegrable
      intervalIntegrable_const, integral_ind, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hmax : ∀ r x : ℝ, max (r - x) 0 = r - min x r := by
    intro r x
    rcases le_total x r with h | h
    · rw [max_eq_left (by linarith), min_eq_left h]
    · rw [max_eq_right (by linarith), min_eq_right h]; ring
  have hj : ∀ j, max ((ω j).2 - ⟪(ω j).1, p⟫) 0 - max ((ω j).2 - ⟪(ω j).1, pstar⟫) 0 =
      ⟪phi d pstar (ω j), p - pstar⟫ - ⟪d, p - pstar⟫ + knightTerm (ω j).1 (ω j).2 p pstar := by
    intro j
    rw [hK, hmax, hmax]
    unfold phi
    rw [inner_sub_left]
    split_ifs with hc
    · rw [inner_sub_right (ω j).1]
      ring
    · rw [inner_zero_left]
      ring
  have hsum : ∑ j, max ((ω j).2 - ⟪(ω j).1, p⟫) 0 - ∑ j, max ((ω j).2 - ⟪(ω j).1, pstar⟫) 0 =
      ∑ j, ⟪phi d pstar (ω j), p - pstar⟫ - (n : ℝ) * ⟪d, p - pstar⟫ +
        ∑ j, knightTerm (ω j).1 (ω j).2 p pstar := by
    rw [← Finset.sum_sub_distrib]
    simp only [hj]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold fn
  have e : ⟪d, p⟫ + 1 / (n : ℝ) * ∑ j, max ((ω j).2 - ⟪(ω j).1, p⟫) 0 -
      (⟪d, pstar⟫ + 1 / (n : ℝ) * ∑ j, max ((ω j).2 - ⟪(ω j).1, pstar⟫) 0) =
      ⟪d, p - pstar⟫ + 1 / (n : ℝ) * (∑ j, max ((ω j).2 - ⟪(ω j).1, p⟫) 0 -
        ∑ j, max ((ω j).2 - ⟪(ω j).1, pstar⟫) 0) := by
    rw [inner_sub_right]; ring
  rw [e, hsum]
  field_simp <;> ring
