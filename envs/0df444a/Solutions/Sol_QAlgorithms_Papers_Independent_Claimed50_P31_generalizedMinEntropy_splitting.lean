-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P31.generalizedMinEntropy_splitting
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:29:51.897093+00:00
-- url     : https://prove2.me/submissions/b09c406b-573e-43bd-b51d-1ed1c35c6056

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P31

noncomputable section
open scoped ENNReal
open Classical

namespace X5MS
open QAlgorithms.Papers.Independent.Claimed50.P31

variable {Omega A B : Type*}

lemma cond_def (p : PMF Omega) (q : Omega → ℝ≥0∞) (X : Omega → A) (Y : Omega → B) (x : A) (y : B)
    (hy : eventProbability p {w | Y w = y} ≠ 0) :
    conditionalRetainedProbability p q X Y x y =
      (∑' w, if X w = x ∧ Y w = y then q w else 0) / eventProbability p {w | Y w = y} := by
  classical
  unfold conditionalRetainedProbability
  rw [if_neg hy]

lemma cond_zero (p : PMF Omega) (q : Omega → ℝ≥0∞) (X : Omega → A) (Y : Omega → B) (x : A) (y : B)
    (hy : eventProbability p {w | Y w = y} = 0) :
    conditionalRetainedProbability p q X Y x y = 0 := by
  classical
  unfold conditionalRetainedProbability
  rw [if_pos hy]

lemma evp_le_one (p : PMF Omega) (E : Set Omega) : eventProbability p E ≤ 1 := by
  classical
  unfold eventProbability
  calc (∑' w, if w ∈ E then p w else 0) ≤ ∑' w, p w :=
        ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp
    _ = 1 := PMF.tsum_coe p

lemma sum_cond_le_one (p : PMF Omega) (X : Omega → A) (Y : Omega → B) (y : B) :
    ∑' x, conditionalRetainedProbability p (fun w => p w) X Y x y ≤ 1 := by
  classical
  by_cases hy : eventProbability p {w | Y w = y} = 0
  · simp [cond_zero p _ X Y _ y hy]
  · simp_rw [cond_def p _ X Y _ y hy, div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_comm]
    have : (∑' w, ∑' x, if X w = x ∧ Y w = y then p w else 0) = eventProbability p {w | Y w = y} := by
      unfold eventProbability
      refine tsum_congr fun w => ?_
      by_cases h : Y w = y
      · simp only [h, and_true, Set.mem_setOf_eq, if_true]
        simp_rw [eq_comm (a := X w)]
        rw [tsum_ite_eq]
      · simp [h]
    rw [this]
    exact ENNReal.mul_inv_le_one _

lemma card_mul_le (p : PMF Omega) (X : Omega → A) (Y : Omega → B) (y : B) (τ : ℝ≥0∞)
    (F : Finset A) (hF : ∀ x ∈ F, τ ≤ conditionalRetainedProbability p (fun w => p w) X Y x y) :
    (F.card : ℝ≥0∞) * τ ≤ 1 := by
  calc (F.card : ℝ≥0∞) * τ = ∑ x ∈ F, τ := by simp
    _ ≤ ∑ x ∈ F, conditionalRetainedProbability p (fun w => p w) X Y x y :=
        Finset.sum_le_sum hF
    _ ≤ ∑' x, conditionalRetainedProbability p (fun w => p w) X Y x y := ENNReal.sum_le_tsum F
    _ ≤ 1 := sum_cond_le_one p X Y y

lemma big_finite (p : PMF Omega) (X : Omega → A) (Y : Omega → B) (y : B) (τ : ℝ≥0∞)
    (hτ : τ ≠ 0) :
    {x | τ ≤ conditionalRetainedProbability p (fun w => p w) X Y x y}.Finite := by
  by_contra hinf
  have hτ' : τ⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hτ
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hτ'
  obtain ⟨F, hFs, hFc⟩ := Set.Infinite.exists_subset_card_eq hinf (N + 1)
  have := card_mul_le p X Y y τ F (fun x hx => hFs hx)
  rw [hFc] at this
  have h2 : (τ⁻¹) * τ ≤ 1 := ENNReal.inv_mul_le_one τ
  have h3 : 1 < ((N + 1 : ℕ) : ℝ≥0∞) * τ := by
    have hτtop : τ ≠ ⊤ := by
      intro h; rw [h] at this
      simp at this
    have hlt : τ⁻¹ < ((N + 1 : ℕ) : ℝ≥0∞) :=
      lt_of_lt_of_le hN (by exact_mod_cast Nat.le_succ N)
    calc (1 : ℝ≥0∞) = τ * τ⁻¹ := (ENNReal.mul_inv_cancel hτ hτtop).symm
      _ < τ * ((N + 1 : ℕ) : ℝ≥0∞) := ENNReal.mul_lt_mul_right hτ hτtop hlt
      _ = ((N + 1 : ℕ) : ℝ≥0∞) * τ := mul_comm _ _
  exact absurd this (not_le.2 h3)

end X5MS


noncomputable section
open scoped ENNReal
open Classical

namespace X5MS
open QAlgorithms.Papers.Independent.Claimed50.P31

theorem main
    (Omega A0 A1 K : Type*) [Nonempty Omega] [Nonempty A0] [Nonempty A1] [Nonempty K]
    (p : PMF Omega) (X0 : Omega → A0) (X1 : Omega → A1) (Kvar : Omega → K)
    (jCount : ℕ) (J : Omega → Fin jCount) (alpha beta epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hbeta : 0 < beta) (hbetaAlpha : beta < alpha)
    (hcard : (jCount : ℝ) = Real.rpow 2 beta)
    (hentropy : (alpha : EReal) ≤ eventSmoothMinEntropy p
      (fun w => (X0 w, X1 w)) (fun w => (Kvar w, J w)) epsilon) :
    (((alpha - beta) / 2 : ℝ) : EReal) ≤ eventSmoothMinEntropy p
      (splittingOutput p X0 X1 Kvar J alpha beta) (fun w => (Kvar w, J w)) epsilon := by
  set KJ : Omega → K × Fin jCount := fun w => (Kvar w, J w) with hKJ
  set τr : ℝ := Real.rpow 2 (-((alpha - beta) / 2)) with hτr_def
  set τ : ℝ≥0∞ := ENNReal.ofReal τr with hτ_def
  have hτr : 0 < τr := Real.rpow_pos_of_pos two_pos _
  have hτ0 : τ ≠ 0 := by simp [τ, hτr]
  have hch : ∀ x1 k, splittingChoice p X1 Kvar J alpha beta x1 k = true ↔
      ∃ j, τ ≤ conditionalRetainedProbability p (fun w => p w) X1 KJ x1 (k, j) := by
    intro x1 k
    unfold splittingChoice
    split_ifs with h <;> simp_all [τ, τr]
  -- the finite set of x1 with choice true, and its size
  have hS : ∀ k, ∃ F : Finset A1,
      (∀ x1, splittingChoice p X1 Kvar J alpha beta x1 k = true ↔ x1 ∈ F) ∧
      (F.card : ℝ) * τr ≤ jCount := by
    intro k
    let T : Fin jCount → Finset A1 := fun j => (big_finite p X1 KJ (k, j) τ hτ0).toFinset
    refine ⟨Finset.univ.biUnion T, fun x1 => ?_, ?_⟩
    · rw [hch]; simp [T]
    · have hT : ∀ j, ((T j).card : ℝ) * τr ≤ 1 := by
        intro j
        have := card_mul_le p X1 KJ (k, j) τ (T j) (fun x hx => by simpa [T] using hx)
        rw [hτ_def, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at this
        exact (ENNReal.ofReal_le_one).1 this
      calc ((Finset.univ.biUnion T).card : ℝ) * τr ≤ (∑ j, ((T j).card : ℝ)) * τr := by
            gcongr
            exact_mod_cast Finset.card_biUnion_le
        _ = ∑ j, ((T j).card : ℝ) * τr := Finset.sum_mul _ _ _
        _ ≤ ∑ _j : Fin jCount, (1 : ℝ) := Finset.sum_le_sum fun j _ => hT j
        _ = jCount := by simp
  -- the key threshold statement
  have key : ∀ h' : ℝ, h' < (alpha - beta) / 2 →
      EventEntropyThreshold p (splittingOutput p X0 X1 Kvar J alpha beta) KJ epsilon h' := by
    intro h' hh'
    set h : ℝ := h' + (alpha + beta) / 2 with hh_def
    have hlt : h < alpha := by rw [hh_def]; linarith
    have hth : EventEntropyThreshold p (fun w => (X0 w, X1 w)) KJ epsilon h := by
      have h1 : (h : EReal) < eventSmoothMinEntropy p (fun w => (X0 w, X1 w)) KJ epsilon :=
        lt_of_lt_of_le (by exact_mod_cast hlt) hentropy
      obtain ⟨t, ⟨h0, rfl, hth0⟩, ht⟩ := lt_sSup_iff.1 h1
      have h0lt : h < h0 := by exact_mod_cast ht
      obtain ⟨q, hqp, hqs, hqb⟩ := hth0
      refine ⟨q, hqp, hqs, fun x y => (hqb x y).trans ?_⟩
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    obtain ⟨q, hqp, hqs, hqb⟩ := hth
    refine ⟨q, hqp, hqs, ?_⟩
    have hτh' : τ ≤ ENNReal.ofReal (Real.rpow 2 (-h')) := by
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rintro ⟨u, c⟩ ⟨k, j⟩
    by_cases hD : eventProbability p {w | KJ w = (k, j)} = 0
    · rw [cond_zero p q _ KJ _ _ hD]; exact zero_le
    rw [cond_def p q _ KJ _ _ hD]
    have hout : ∀ w, splittingOutput p X0 X1 Kvar J alpha beta w =
        (if splittingChoice p X1 Kvar J alpha beta (X1 w) (Kvar w) then Sum.inl (X0 w)
          else Sum.inr (X1 w), splittingChoice p X1 Kvar J alpha beta (X1 w) (Kvar w)) := by
      intro w; rfl
    cases c
    · cases u with
      | inl x0 =>
        refine le_of_eq_of_le ?_ zero_le
        rw [ENNReal.div_eq_zero_iff]; left
        refine ENNReal.tsum_eq_zero.2 fun w => if_neg ?_
        rw [hout]
        cases hcw : splittingChoice p X1 Kvar J alpha beta (X1 w) (Kvar w) <;> simp
      | inr x1 =>
        by_cases hc : splittingChoice p X1 Kvar J alpha beta x1 k = true
        · refine le_of_eq_of_le ?_ zero_le
          rw [ENNReal.div_eq_zero_iff]; left
          refine ENNReal.tsum_eq_zero.2 fun w => if_neg ?_
          rw [hout]
          rintro ⟨h1, h2⟩
          simp only [KJ, Prod.mk.injEq] at h2
          obtain ⟨hk, -⟩ := h2
          cases hw : splittingChoice p X1 Kvar J alpha beta (X1 w) (Kvar w)
          · rw [hw] at h1
            simp only [Bool.false_eq_true, if_false, Prod.mk.injEq, Sum.inr.injEq] at h1
            rw [h1.1, hk] at hw
            rw [hw] at hc
            exact absurd hc (by simp)
          · rw [hw] at h1
            simp at h1
        · have hc' : conditionalRetainedProbability p (fun w => p w) X1 KJ x1 (k, j) < τ := by
            by_contra hn
            exact hc ((hch x1 k).2 ⟨j, not_lt.1 hn⟩)
          rw [cond_def p _ X1 KJ _ _ hD] at hc'
          refine le_trans ?_ (le_trans hc'.le hτh')
          gcongr with w
          rw [hout]
          by_cases hw : X1 w = x1 ∧ KJ w = (k, j)
          · rw [if_pos hw]; split_ifs <;> simp [hqp w]
          · rw [if_neg hw, if_neg]
            rintro ⟨h1, h2⟩
            apply hw
            refine ⟨?_, h2⟩
            cases hcw : splittingChoice p X1 Kvar J alpha beta (X1 w) (Kvar w) <;>
              simp_all
    · cases u with
      | inr x1 =>
        refine le_of_eq_of_le ?_ zero_le
        rw [ENNReal.div_eq_zero_iff]; left
        refine ENNReal.tsum_eq_zero.2 fun w => if_neg ?_
        rw [hout]
        cases hcw : splittingChoice p X1 Kvar J alpha beta (X1 w) (Kvar w) <;> simp
      | inl x0 =>
        obtain ⟨F, hF, hFc⟩ := hS k
        have hsplit : ∀ w, (if splittingOutput p X0 X1 Kvar J alpha beta w = (Sum.inl x0, true) ∧
            KJ w = (k, j) then q w else 0) =
            ∑ x1 ∈ F, (if (X0 w, X1 w) = (x0, x1) ∧ KJ w = (k, j) then q w else 0) := by
          intro w
          have e : ∀ x1, ((X0 w, X1 w) = (x0, x1) ∧ KJ w = (k, j)) ↔
              (X1 w = x1 ∧ (X0 w = x0 ∧ KJ w = (k, j))) := by
            intro x1; simp only [Prod.mk.injEq]; tauto
          simp_rw [e, ite_and]
          rw [Finset.sum_ite_eq]
          rw [hout]
          by_cases hkj : KJ w = (k, j)
          · have hk : Kvar w = k := by simp only [KJ, Prod.mk.injEq] at hkj; exact hkj.1
            rw [hk]
            by_cases hm : X1 w ∈ F
            · have hc1 := (hF (X1 w)).2 hm
              simp [hc1, hm, hkj]
            · have hc0 : splittingChoice p X1 Kvar J alpha beta (X1 w) k = false := by
                simpa using mt (hF (X1 w)).1 hm
              simp [hc0, hm]
          · simp [hkj]
        refine le_trans (le_of_eq ?_) (?_ : (∑ x1 ∈ F, (∑' w, if (X0 w, X1 w) = (x0, x1) ∧
            KJ w = (k, j) then q w else 0)) / eventProbability p {w | KJ w = (k, j)} ≤ _)
        · congr 1
          rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          exact tsum_congr fun w => by convert hsplit w
        rw [div_eq_mul_inv, Finset.sum_mul]
        calc ∑ x1 ∈ F, (∑' w, if (X0 w, X1 w) = (x0, x1) ∧ KJ w = (k, j) then q w else 0) *
              (eventProbability p {w | KJ w = (k, j)})⁻¹
            ≤ ∑ _x1 ∈ F, ENNReal.ofReal (Real.rpow 2 (-h)) := by
              refine Finset.sum_le_sum fun x1 _ => ?_
              have := hqb (x0, x1) (k, j)
              rw [cond_def p q _ KJ _ _ hD, div_eq_mul_inv] at this
              refine le_trans (le_of_eq ?_) this
              congr 2
              funext w
              split_ifs <;> rfl
          _ = ENNReal.ofReal (F.card * Real.rpow 2 (-h)) := by
              rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg F.card),
                ENNReal.ofReal_natCast]
          _ ≤ ENNReal.ofReal (Real.rpow 2 (-h')) := by
              apply ENNReal.ofReal_le_ofReal
              have hinv : τr * Real.rpow 2 ((alpha - beta) / 2) = 1 := by
                rw [hτr_def, Real.rpow_eq_pow, Real.rpow_eq_pow, ← Real.rpow_add two_pos]; simp
              have hF' : (F.card : ℝ) ≤ Real.rpow 2 beta * Real.rpow 2 ((alpha - beta) / 2) := by
                have h2pos : 0 < Real.rpow 2 ((alpha - beta) / 2) := Real.rpow_pos_of_pos two_pos _
                calc (F.card : ℝ) = (F.card * τr) * Real.rpow 2 ((alpha - beta) / 2) := by
                      rw [mul_assoc, hinv, mul_one]
                  _ ≤ jCount * Real.rpow 2 ((alpha - beta) / 2) := by gcongr
                  _ = _ := by rw [hcard]
              have he : Real.rpow 2 beta * Real.rpow 2 ((alpha - beta) / 2) * Real.rpow 2 (-h) =
                  Real.rpow 2 (-h') := by
                simp only [Real.rpow_eq_pow]
                rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos, hh_def]
                congr 1; ring
              rw [← he]
              gcongr
              exact Real.rpow_nonneg (by norm_num) _
  -- conclude
  apply le_of_forall_lt
  intro c hc
  obtain ⟨x, hcx, hx⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  refine lt_of_lt_of_le hcx (le_sSup ⟨x, rfl, key x (by exact_mod_cast hx)⟩)

end X5MS

open QAlgorithms.Papers.Independent.Claimed50.P31 in
theorem solution
    (Omega A0 A1 K : Type*) [Nonempty Omega] [Nonempty A0] [Nonempty A1] [Nonempty K]
    (p : PMF Omega) (X0 : Omega → A0) (X1 : Omega → A1) (Kvar : Omega → K)
    (jCount : ℕ) (J : Omega → Fin jCount) (alpha beta epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hbeta : 0 < beta) (hbetaAlpha : beta < alpha)
    (hcard : (jCount : ℝ) = Real.rpow 2 beta)
    (hentropy : (alpha : EReal) ≤ eventSmoothMinEntropy p
      (fun w => (X0 w, X1 w)) (fun w => (Kvar w, J w)) epsilon) :
    (((alpha - beta) / 2 : ℝ) : EReal) ≤ eventSmoothMinEntropy p
      (splittingOutput p X0 X1 Kvar J alpha beta) (fun w => (Kvar w, J w)) epsilon :=
  X5MS.main Omega A0 A1 K p X0 X1 Kvar jCount J alpha beta epsilon hepsilon hbeta hbetaAlpha
    hcard hentropy
