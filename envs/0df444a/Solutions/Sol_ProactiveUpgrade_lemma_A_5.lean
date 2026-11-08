-- Prove2me | solution 1 for ProactiveUpgrade.lemma_A_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:12:08.45021+00:00
-- url     : https://prove2.me/submissions/48f87f4c-1cf9-4412-add8-990c5c5477ce

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model
import Definitions.Def_ProactiveUpgrade_vhat
import Definitions.Def_ProactiveUpgrade_IsValid

namespace ProactiveUpgrade.Aux_PU

open ProactiveUpgrade

theorem dec_self {m : ℕ} (x : Fin m → ℕ) (i : Fin m) : dec x i i = x i - 1 := by
  simp [dec]

theorem dec_ne {m : ℕ} (x : Fin m → ℕ) {i j : Fin m} (h : j ≠ i) : dec x i j = x j := by
  simp [dec, h]

theorem dec_comm {m : ℕ} (x : Fin m → ℕ) {i j : Fin m} (h : j ≠ i) :
    dec (dec x i) j = dec (dec x j) i := by
  unfold dec
  rw [Function.update_apply, if_neg h, Function.update_apply, if_neg (Ne.symm h)]
  exact Function.update_comm (Ne.symm h) _ _ _

theorem dec_of_zero {m : ℕ} (x : Fin m → ℕ) (i : Fin m) (h : x i = 0) : dec x i = x := by
  unfold dec
  rw [h]
  exact Function.update_eq_self_iff.mpr (by simp [h])

theorem dec_le {m : ℕ} (x : Fin m → ℕ) (i j : Fin m) : dec x i j ≤ x j := by
  by_cases h : j = i
  · subst h; rw [dec_self]; omega
  · rw [dec_ne x h]

theorem step_bound {m : ℕ} (M : Model m) (hM : IsValid M) (f : (Fin m → ℕ) → ℝ)
    (H : ∀ x i, 0 < x i → f x < f (dec x i) + M.p i) (x : Fin m → ℕ) (i : Fin m)
    (hx : 0 < x i) : step M f x < step M f (dec x i) + M.p i := by
  set y := dec x i with hy
  have hpi := hM.p_pos i
  have hN : ∀ j, noOfferVal M f x j ≤ noOfferVal M f y j + M.p i := by
    intro j
    unfold noOfferVal
    by_cases hji : j = i
    · subst hji
      rw [if_neg (by omega)]
      by_cases hy0 : y j = 0
      · rw [if_pos hy0]
      · rw [if_neg hy0]
        have := H y j (Nat.pos_of_ne_zero hy0)
        linarith
    · have hyj : y j = x j := dec_ne x hji
      rw [hyj]
      by_cases hx0 : x j = 0
      · rw [if_pos hx0, if_pos hx0]
        exact (H x i hx).le
      · rw [if_neg hx0, if_neg hx0, hy, dec_comm x hji]
        have h1 := H (dec x j) i (by rw [dec_ne x (Ne.symm hji)]; exact hx)
        linarith
  have hF : ∀ k, f (dec x k) ≤ f (dec y k) + M.p i := by
    intro k
    by_cases hki : k = i
    · subst hki
      by_cases hpos : 0 < y k
      · exact (H y k hpos).le
      · have hy0 : y k = 0 := by omega
        rw [dec_of_zero y k hy0]
        linarith
    · rw [hy, dec_comm x hki]
      exact (H (dec x k) i (by rw [dec_ne x (Ne.symm hki)]; exact hx)).le
  have hO : ∀ j (h : j.val + 1 < m), offerVal M f x j h ≤ offerVal M f y j h + M.p i := by
    intro j h
    obtain ⟨hq0, hq1⟩ := hM.q_mem j h
    unfold offerVal
    have a1 := mul_le_mul_of_nonneg_left (hF (succIdx j h)) hq0
    have a2 := mul_le_mul_of_nonneg_left (hN j) (sub_nonneg.mpr hq1)
    nlinarith
  have hX : ∀ j (h : j.val + 1 < m), succIdx j h = i →
      offerVal M f x j h ≤ noOfferVal M f y j + M.p i := by
    intro j h hk
    obtain ⟨hq0, hq1⟩ := hM.q_mem j h
    have hji : j ≠ i := by
      intro e; rw [← hk] at e
      have := congrArg Fin.val e
      simp [succIdx] at this
    have hjlt : j < i := by
      rw [← hk]; rw [Fin.lt_def]; simp [succIdx]
    have hpj := hM.p_strictMono hjlt
    have key : f (dec x (succIdx j h)) + M.p j ≤ noOfferVal M f y j + M.p i := by
      rw [hk]
      unfold noOfferVal
      by_cases hy0 : y j = 0
      · rw [if_pos hy0]; linarith
      · rw [if_neg hy0]
        have := H y j (Nat.pos_of_ne_zero hy0)
        linarith
    unfold offerVal
    have a1 := mul_le_mul_of_nonneg_left key hq0
    have a2 := mul_le_mul_of_nonneg_left (hN j) (sub_nonneg.mpr hq1)
    nlinarith
  have hR : ∀ j, reqOp M f x j ≤ reqOp M f y j + M.p i := by
    intro j
    unfold reqOp
    by_cases h : j.val + 1 < m
    · rw [dif_pos h, dif_pos h]
      by_cases hxk : x (succIdx j h) = 0
      · have hyk : y (succIdx j h) = 0 := by
          have := dec_le x i (succIdx j h)
          rw [← hy] at this
          omega
        rw [if_pos hxk, if_pos hyk]
        exact hN j
      · rw [if_neg hxk]
        by_cases hyk : y (succIdx j h) = 0
        · rw [if_pos hyk]
          have hk : succIdx j h = i := by
            by_contra hne
            rw [hy, dec_ne x hne] at hyk
            exact hxk hyk
          exact max_le (hN j) (hX j h hk)
        · rw [if_neg hyk]
          apply max_le
          · exact (hN j).trans (by linarith [le_max_left (noOfferVal M f y j) (offerVal M f y j h)])
          · exact (hO j h).trans (by linarith [le_max_right (noOfferVal M f y j) (offerVal M f y j h)])
    · rw [dif_neg h, dif_neg h]
      exact hN j
  obtain ⟨hl0, hl1⟩ := hM.lam_mem
  have hβs : 0 ≤ ∑ j, M.β j := Finset.sum_nonneg fun j _ => hM.β_nonneg j
  have hsum1 := hM.sum_eq_one
  have hβ0 := hM.β0_pos
  have hc : 0 < M.lam * M.β0 + (1 - M.lam) := by
    nlinarith [mul_le_mul_of_nonneg_right hl1 hβs]
  have hsum : ∑ j, M.lam * M.β j * reqOp M f x j ≤
      ∑ j, M.lam * M.β j * reqOp M f y j + (∑ j, M.lam * M.β j) * M.p i := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have hw : 0 ≤ M.lam * M.β j := mul_nonneg hl0 (hM.β_nonneg j)
    have := mul_le_mul_of_nonneg_left (hR j) hw
    linarith
  have hw : ∑ j, M.lam * M.β j = M.lam * ∑ j, M.β j := by rw [Finset.mul_sum]
  have hlast := mul_lt_mul_of_pos_left (H x i hx) hc
  unfold step
  rw [hw] at hsum
  have htot : M.lam * (∑ j, M.β j) + (M.lam * M.β0 + (1 - M.lam)) = 1 := by
    have : ∑ j, M.β j = 1 - M.β0 := by linarith
    rw [this]; ring
  nlinarith

theorem main {m : ℕ} (M : Model m) (hM : IsValid M) (n : ℕ) :
    ∀ x i, 0 < x i → valueToGo M n x < valueToGo M n (dec x i) + M.p i := by
  induction n with
  | zero =>
    intro x i _
    simp only [valueToGo]
    linarith [hM.p_pos i]
  | succ n ih =>
    intro x i hx
    exact step_bound M hM (valueToGo M n) ih x i hx

end ProactiveUpgrade.Aux_PU

open ProactiveUpgrade ProactiveUpgrade.Aux_PU in
theorem solution {m : ℕ} (M : Model m) (hM : IsValid M) (T t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ T)
    (i : Fin m) (x : Fin m → ℕ) (hx : 0 < x i) :
    vhat M T t x < vhat M T t (dec x i) + M.p i := by
  unfold vhat
  exact main M hM (T + 1 - t) x i hx
