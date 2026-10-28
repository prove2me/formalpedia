-- Prove2me | solution 1 for ShadowTomography.ClassicalLB.entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T16:14:57.476686+00:00
-- url     : https://prove2.me/submissions/087bd16b-4d18-4439-8d6e-d9499676bbb6

import Mathlib
import Definitions.Def_WildeQIT_entropy
import Definitions.Def_ShadowTomography_ClassicalLB_biasedDist

set_option autoImplicit false

namespace EB_bbdac246

lemma tlog (t : ℝ) (ht : 0 ≤ t) : t * Real.log t + t * Real.log 2 ≤ t * (2 * t - 1) := by
  rcases ht.eq_or_lt with h | h
  · subst h; simp
  · have h1 : Real.log (2 * t) ≤ 2 * t - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_mul (by norm_num) h.ne'] at h1
    nlinarith

lemma sum_ite_const {N : ℕ} (S : Finset (Fin N)) (A B : ℝ) :
    ∑ x : Fin N, (if x ∈ S then A else B) = S.card * A + (N - S.card) * B := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have h1 : (Finset.univ.filter (fun x : Fin N => x ∈ S)) = S := by ext; simp
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (fun x : Fin N => x ∈ S)
  rw [h1, Finset.card_univ, Fintype.card_fin] at h2
  rw [h1]
  have h3 : ((Finset.univ.filter (fun x : Fin N => ¬ x ∈ S)).card : ℝ) = N - S.card := by
    have h2r : ((S.card : ℕ) : ℝ) +
        ((Finset.univ.filter (fun x : Fin N => ¬ x ∈ S)).card : ℝ) = N := by exact_mod_cast h2
    linarith
  rw [h3]

lemma mul_logb_div (t k : ℝ) (hk : 0 < k) :
    t * Real.logb 2 (t / k) = t * Real.logb 2 t - t * Real.logb 2 k := by
  rcases eq_or_ne t 0 with h | h
  · subst h; simp
  · rw [Real.logb_div h hk.ne']; ring

end EB_bbdac246

open ShadowTomography.ClassicalLB in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (S : Finset (Fin N)) (ε : ℝ),
      2 * S.card = N → 1 ≤ S.card → 0 ≤ ε → ε ≤ 1 / 6 →
      ∃ p : WildeQIT.FinDist (Fin N),
        (∀ x, p.prob x = biasedDist N S ε x) ∧
        WildeQIT.entropy p = Real.logb 2 N -
          (1 - (1 / 2 + 3 * ε) * Real.logb 2 (1 / (1 / 2 + 3 * ε)) -
            (1 / 2 - 3 * ε) * Real.logb 2 (1 / (1 / 2 - 3 * ε))) ∧
        Real.logb 2 N - C * ε ^ 2 ≤ WildeQIT.entropy p := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨36 / Real.log 2, by positivity, ?_⟩
  intro N S ε hN hS hε0 hε1
  have hk : (0 : ℝ) < S.card := by exact_mod_cast hS
  have hNr : (N : ℝ) = 2 * S.card := by exact_mod_cast hN.symm
  have hN2 : ((N : ℝ) / 2) = S.card := by rw [hNr]; ring
  have ha0 : 0 < 1 / 2 + 3 * ε := by linarith
  have hb0 : 0 ≤ 1 / 2 - 3 * ε := by linarith
  have hform : ∀ x, biasedDist N S ε x =
      if x ∈ S then (1 / 2 + 3 * ε) / S.card else (1 / 2 - 3 * ε) / S.card := by
    intro x; unfold biasedDist; rw [hN2]
  have hprob : ∀ x, 0 ≤ biasedDist N S ε x := by
    intro x; rw [hform]; split_ifs <;> positivity
  have hsum : ∑ x, biasedDist N S ε x = 1 := by
    simp_rw [hform]
    rw [EB_bbdac246.sum_ite_const, hNr]
    field_simp
    ring
  let p : WildeQIT.FinDist (Fin N) := ⟨biasedDist N S ε, hprob, hsum⟩
  have hent : WildeQIT.entropy p =
      -((1 / 2 + 3 * ε) * Real.logb 2 ((1 / 2 + 3 * ε) / S.card) +
        (1 / 2 - 3 * ε) * Real.logb 2 ((1 / 2 - 3 * ε) / S.card)) := by
    unfold WildeQIT.entropy
    show -∑ x, biasedDist N S ε x * Real.logb 2 (biasedDist N S ε x) = _
    have : ∀ x, biasedDist N S ε x * Real.logb 2 (biasedDist N S ε x) =
        if x ∈ S then (1 / 2 + 3 * ε) / S.card * Real.logb 2 ((1 / 2 + 3 * ε) / S.card)
        else (1 / 2 - 3 * ε) / S.card * Real.logb 2 ((1 / 2 - 3 * ε) / S.card) := by
      intro x; rw [hform]; split_ifs <;> rfl
    simp_rw [this]
    rw [EB_bbdac246.sum_ite_const, hNr]
    field_simp
    ring
  have hlogN : Real.logb 2 N = 1 + Real.logb 2 S.card := by
    rw [hNr, Real.logb_mul (by norm_num) hk.ne', Real.logb_self_eq_one (by norm_num)]
  have hE : WildeQIT.entropy p = Real.logb 2 N -
      (1 - (1 / 2 + 3 * ε) * Real.logb 2 (1 / (1 / 2 + 3 * ε)) -
        (1 / 2 - 3 * ε) * Real.logb 2 (1 / (1 / 2 - 3 * ε))) := by
    rw [hent, hlogN, EB_bbdac246.mul_logb_div _ _ hk, EB_bbdac246.mul_logb_div _ _ hk,
      one_div (1 / 2 + 3 * ε), one_div (1 / 2 - 3 * ε), Real.logb_inv, Real.logb_inv]
    ring
  refine ⟨p, fun x => rfl, hE, ?_⟩
  rw [hE]
  have ta := EB_bbdac246.tlog _ ha0.le
  have tb := EB_bbdac246.tlog _ hb0
  rw [one_div (1 / 2 + 3 * ε), one_div (1 / 2 - 3 * ε), Real.logb_inv, Real.logb_inv]
  unfold Real.logb
  have key : Real.log 2 + (1 / 2 + 3 * ε) * Real.log (1 / 2 + 3 * ε) +
      (1 / 2 - 3 * ε) * Real.log (1 / 2 - 3 * ε) ≤ 36 * ε ^ 2 := by nlinarith
  have : 36 / Real.log 2 * ε ^ 2 = (36 * ε ^ 2) / Real.log 2 := by ring
  rw [this]
  have h2 : (Real.log 2 + (1 / 2 + 3 * ε) * Real.log (1 / 2 + 3 * ε) +
      (1 / 2 - 3 * ε) * Real.log (1 / 2 - 3 * ε)) / Real.log 2 ≤ (36 * ε ^ 2) / Real.log 2 :=
    div_le_div_of_nonneg_right key hl2.le
  have h3 : (Real.log 2 + (1 / 2 + 3 * ε) * Real.log (1 / 2 + 3 * ε) +
      (1 / 2 - 3 * ε) * Real.log (1 / 2 - 3 * ε)) / Real.log 2 =
      1 + (1 / 2 + 3 * ε) * (Real.log (1 / 2 + 3 * ε) / Real.log 2) +
      (1 / 2 - 3 * ε) * (Real.log (1 / 2 - 3 * ε) / Real.log 2) := by
    field_simp
  linarith
