-- Prove2me | solution 1 for RegretPricing.Structure.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T16:07:06.763059+00:00
-- url     : https://prove2.me/submissions/e2d2be96-5434-45b5-8b40-c03089013f9e

import Mathlib
import Definitions.Def_RegretPricing_Structure_Model
import Theorems.Thm_RegretPricing_Structure_proposition_4a
import Theorems.Thm_RegretPricing_Structure_proposition_1a
import Theorems.Thm_RegretPricing_Structure_regret_price_mono
import Theorems.Thm_RegretPricing_Structure_lemma_1
import Theorems.Thm_RegretPricing_Structure_unbiased_price_unique

open RegretPricing.Structure MeasureTheory

theorem solution (D : WTP) (hD : D.Standing) (hIFR : D.IFR) (α β lam : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) (hlam : 0 ≤ lam ∧ lam ≤ 1 / 2)
    (hm : AntitoneOn (regretValue D α β) (Set.Icc 0 D.b)) :
    (∀ t x : ℕ, 1 ≤ x → dU D α β lam t x ≤ dU D α β lam (t + 1) x) ∧
      (∀ t x : ℕ, 1 ≤ x → dU D α β lam t (x + 1) ≤ dU D α β lam t x) ∧
      (∀ t x : ℕ, 1 ≤ x → ∃! p, IsRegretPrice D α β (dU D α β lam t x) p) ∧
      (∀ t x : ℕ, 1 ≤ x → ∀ p p', IsRegretPrice D α β (dU D α β lam t x) p →
        IsRegretPrice D α β (dU D α β lam (t + 1) x) p' → p ≤ p') ∧
      (∀ t x : ℕ, 1 ≤ x → ∀ p p', IsRegretPrice D α β (dU D α β lam t (x + 1)) p →
        IsRegretPrice D α β (dU D α β lam t x) p' → p ≤ p') := by
  obtain ⟨ha0, hab, hf0, hfout, hfint, hf1, -⟩ := id hD
  obtain ⟨h4t, h4x⟩ := proposition_4a D hD hIFR α β lam hα hβ hlam hm
  -- basic facts on the distribution function
  have hF0 : ∀ x, 0 ≤ D.F x := fun x =>
    setIntegral_nonneg measurableSet_Iic (fun t _ => hf0 t)
  have hF1 : ∀ x, D.F x ≤ 1 := fun x => by
    have := setIntegral_le_integral (s := Set.Iic x) hfint (Filter.Eventually.of_forall hf0)
    unfold WTP.F; linarith
  have hFb : ∀ x, D.b ≤ x → D.F x = 1 := fun x hx => by
    unfold WTP.F
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hf1]
    intro t ht
    apply hfout
    intro h; exact ht (Set.mem_Iic.2 (le_trans h.2 hx))
  have hFa : ∀ x, x < D.a → D.F x = 0 := fun x hx => by
    unfold WTP.F
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    apply hfout
    intro h; exact absurd (lt_of_le_of_lt (le_trans h.1 ht) hx) (lt_irrefl _)
  -- revenue bound
  have hrev : ∀ z, z ≤ D.b → ∀ y, revenue D y z ≤ D.b - z := by
    intro z hz y
    unfold revenue WTP.Fbar
    by_cases hy : D.b ≤ y
    · rw [hFb y hy]; simp; linarith
    · push_neg at hy
      by_cases hyz : z ≤ y
      · have := hF0 y
        nlinarith [mul_le_mul_of_nonneg_left (show 1 - D.F y ≤ 1 by linarith)
          (show 0 ≤ y - z by linarith)]
      · push_neg at hyz
        have := hF1 y
        nlinarith [mul_nonneg (show 0 ≤ z - y by linarith) (show 0 ≤ 1 - D.F y by linarith)]
  -- bound on the regret value
  have hV : ∀ z, 0 ≤ z → z < D.b → regretValue D α β z ≤ D.b - z := by
    intro z hz0 hzb
    obtain ⟨⟨phat, hphat, -⟩, -⟩ :=
      proposition_1a D hD hIFR α β hα hβ z ⟨hz0, hzb⟩
    have hle : regretValue D α β z ≤ πhat D α β phat z := ciSup_le (fun p => hphat p)
    obtain ⟨⟨pstar, hpstar, -⟩, -⟩ :=
      unbiased_price_unique D hD hIFR z ⟨hz0, hzb⟩
    obtain ⟨hro, -, -⟩ :=
      lemma_1 D hD hIFR z ⟨hz0, hzb.le⟩ pstar hpstar
    -- r_o ≥ 0
    have hro0 : ro D (min phat (D.a - 1)) z = 0 := by
      unfold ro
      have : (fun y : {y : ℝ // y < min phat (D.a - 1)} =>
          (y.1 - z) * (D.Fbar y.1 - D.Fbar (min phat (D.a - 1)))) = fun _ => 0 := by
        funext y
        have h1 : y.1 < D.a := by
          have := y.2; have := min_le_right phat (D.a - 1); linarith
        have h2 : min phat (D.a - 1) < D.a := by
          have := min_le_right phat (D.a - 1); linarith
        simp [WTP.Fbar, hFa _ h1, hFa _ h2]
      rw [this]
      haveI : Nonempty {y : ℝ // y < min phat (D.a - 1)} := ⟨⟨min phat (D.a - 1) - 1, by linarith⟩⟩
      exact ciSup_const
    have hroge : 0 ≤ ro D phat z := hro0 ▸ hro (min_le_left _ _)
    -- r_u ≥ 0
    have hruge : 0 ≤ ru D phat z := by
      unfold ru
      have hb : BddAbove (Set.range fun y : {y : ℝ // phat ≤ y} => revenue D y.1 z) :=
        ⟨D.b - z, by rintro _ ⟨y, rfl⟩; exact hrev z hzb.le y.1⟩
      have := le_ciSup hb ⟨phat, le_refl _⟩
      simp only at this
      linarith
    have : πhat D α β phat z ≤ revenue D phat z := by
      unfold πhat
      nlinarith [mul_nonneg hα.1 hroge, mul_nonneg hβ.1 hruge]
    linarith [hrev z hzb.le phat]
  -- U_t(0) = 0
  have hU0 : ∀ t, U D α β lam t 0 = 0 := by
    intro t; cases t <;> rfl
  -- lower bound
  have hlow : ∀ t x, 1 ≤ x → 0 ≤ dU D α β lam t x := by
    intro t x hx
    induction t with
    | zero => simp [dU, U]
    | succ t ih => exact le_trans ih (h4t t x hx)
  -- upper bound at x = 1
  have hup1 : ∀ t, dU D α β lam t 1 < D.b := by
    intro t
    induction t with
    | zero => simp [dU, U]; linarith
    | succ t ih =>
      have hz0 := hlow t 1 le_rfl
      have e1 : dU D α β lam t 1 = U D α β lam t 1 := by simp [dU, hU0]
      have e2 : dU D α β lam (t + 1) 1 =
          U D α β lam t 1 + lam * regretValue D α β (dU D α β lam t 1) := by
        simp [dU, hU0, U]
      rw [e2, ← e1]
      have hv := hV _ hz0 ih
      have : lam * regretValue D α β (dU D α β lam t 1) ≤ lam * (D.b - dU D α β lam t 1) :=
        mul_le_mul_of_nonneg_left hv hlam.1
      nlinarith
  have hup : ∀ t x, 1 ≤ x → dU D α β lam t x < D.b := by
    intro t x hx
    induction x, hx using Nat.le_induction with
    | base => exact hup1 t
    | succ x hx ih => exact lt_of_le_of_lt (h4x t x hx) ih
  refine ⟨h4t, h4x, ?_, ?_, ?_⟩
  · intro t x hx
    exact (proposition_1a D hD hIFR α β hα hβ _ ⟨hlow t x hx, hup t x hx⟩).1
  · intro t x hx p p' hp hp'
    exact regret_price_mono D hD hIFR α β hα hβ _ _ (hlow t x hx) (h4t t x hx)
      (hup (t + 1) x hx) p p' hp hp'
  · intro t x hx p p' hp hp'
    exact regret_price_mono D hD hIFR α β hα hβ _ _ (hlow t (x + 1) (by omega)) (h4x t x hx)
      (hup t x hx) p p' hp hp'
