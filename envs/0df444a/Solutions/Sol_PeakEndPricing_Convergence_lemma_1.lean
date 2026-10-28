-- Prove2me | solution 1 for PeakEndPricing.Convergence.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:44:49.479914+00:00
-- url     : https://prove2.me/submissions/034ad1c4-e0f9-4721-abfb-b3808a88214f

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model

namespace Aux_PeakEndPricing_Convergence_lemma_1

open PeakEndPricing.Convergence

lemma minPrice_mem (pbar m0 : ℝ) (q : ℕ → ℝ) (hm0 : m0 ∈ Set.Icc (0 : ℝ) pbar)
    (hq : ∀ n, q n ∈ Set.Icc (0 : ℝ) pbar) : ∀ n, minPrice m0 q n ∈ Set.Icc (0 : ℝ) pbar := by
  intro n
  induction n with
  | zero => exact hm0
  | succ n ih =>
    simp only [minPrice]
    exact ⟨le_min ih.1 (hq n).1, (min_le_left _ _).trans ih.2⟩

lemma minPrice_mono (m0 m0' : ℝ) (q : ℕ → ℝ) (h : m0 ≤ m0') :
    ∀ n, minPrice m0 q n ≤ minPrice m0' q n := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [minPrice]
    exact min_le_min ih le_rfl

lemma price_mem (pbar p0 : ℝ) (q : ℕ → ℝ) (hp0 : p0 ∈ Set.Icc (0 : ℝ) pbar)
    (hq : ∀ n, q n ∈ Set.Icc (0 : ℝ) pbar) : ∀ n, price p0 q n ∈ Set.Icc (0 : ℝ) pbar := by
  intro n
  cases n with
  | zero => exact hp0
  | succ n => exact hq n

lemma price_mono (p0 p0' : ℝ) (q : ℕ → ℝ) (h : p0 ≤ p0') :
    ∀ n, price p0 q n ≤ price p0' q n := by
  intro n
  cases n with
  | zero => exact h
  | succ n => exact le_rfl

lemma profit_mono (d0 : ℝ → ℝ) (lam gam p r r' : ℝ) (hlam : 0 ≤ lam) (hgam : 0 ≤ gam)
    (hp : 0 ≤ p) (hr : r ≤ r') : profit d0 lam gam p r ≤ profit d0 lam gam p r' := by
  unfold profit demand
  apply mul_le_mul_of_nonneg_left _ hp
  have h1 : max (p - r') 0 ≤ max (p - r) 0 := max_le_max (by linarith) le_rfl
  have h2 : max (r - p) 0 ≤ max (r' - p) 0 := max_le_max (by linarith) le_rfl
  nlinarith [mul_le_mul_of_nonneg_left h1 hlam, mul_le_mul_of_nonneg_left h2 hgam]

lemma profit_bound (pbar D : ℝ) (d0 : ℝ → ℝ) (lam gam p r : ℝ) (hlam : 0 ≤ lam) (hgam : 0 ≤ gam)
    (hp : p ∈ Set.Icc (0 : ℝ) pbar) (hr : r ∈ Set.Icc (0 : ℝ) pbar)
    (hd : 0 ≤ d0 p) (hD : d0 p ≤ D) :
    |profit d0 lam gam p r| ≤ pbar * (D + lam * pbar + gam * pbar) := by
  unfold profit demand
  have a1 : 0 ≤ max (p - r) 0 := le_max_right _ _
  have a2 : max (p - r) 0 ≤ pbar := max_le (by linarith [hr.1, hp.2]) (by linarith [hp.1, hp.2])
  have b1 : 0 ≤ max (r - p) 0 := le_max_right _ _
  have b2 : max (r - p) 0 ≤ pbar := max_le (by linarith [hr.2, hp.1]) (by linarith [hp.1, hp.2])
  have hp0 := hp.1
  have hp1 := hp.2
  rw [abs_le]
  constructor
  · have : -(lam * pbar) ≤ d0 p - lam * max (p - r) 0 + gam * max (r - p) 0 := by
      nlinarith [mul_le_mul_of_nonneg_left a2 hlam, mul_nonneg hgam b1]
    have hC : 0 ≤ D + gam * pbar := by nlinarith [mul_nonneg hgam (hp0.trans hp1)]
    nlinarith [mul_le_mul_of_nonneg_left this hp0, mul_le_mul_of_nonneg_right hp1
      (mul_nonneg hlam (hp0.trans hp1)), mul_nonneg (hp0.trans hp1) hC]
  · have : d0 p - lam * max (p - r) 0 + gam * max (r - p) 0 ≤ D + gam * pbar := by
      nlinarith [mul_nonneg hlam a1, mul_le_mul_of_nonneg_left b2 hgam]
    have hC : 0 ≤ D + gam * pbar := by nlinarith [mul_nonneg hgam (hp0.trans hp1)]
    nlinarith [mul_le_mul_of_nonneg_left this hp0, mul_le_mul_of_nonneg_right hp1 hC,
      mul_nonneg (hp0.trans hp1) (mul_nonneg hlam (hp0.trans hp1))]

end Aux_PeakEndPricing_Convergence_lemma_1

open Aux_PeakEndPricing_Convergence_lemma_1 in
open PeakEndPricing.Convergence in
theorem solution (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ)
    (hst : Standing pbar d0 lam gam theta beta) :
    (∀ m m' p : ℝ, m ∈ Set.Icc (0 : ℝ) pbar → m' ∈ Set.Icc (0 : ℝ) pbar →
      p ∈ Set.Icc (0 : ℝ) pbar → m ≤ m' →
        J pbar d0 lam gam theta beta m p ≤ J pbar d0 lam gam theta beta m' p) ∧
    (∀ m p p' : ℝ, m ∈ Set.Icc (0 : ℝ) pbar → p ∈ Set.Icc (0 : ℝ) pbar →
      p' ∈ Set.Icc (0 : ℝ) pbar → p ≤ p' →
        J pbar d0 lam gam theta beta m p ≤ J pbar d0 lam gam theta beta m p') := by
  obtain ⟨D, hD⟩ := hst.assumption1.bounded
  have hlam : 0 ≤ lam := le_trans hst.gam_pos.le hst.gam_le_lam
  have hgam : 0 ≤ gam := hst.gam_pos.le
  have hth0 : 0 ≤ theta := hst.theta_pos.le
  have hth1 : 0 ≤ 1 - theta := by linarith [hst.theta_le_one]
  have hb0 : 0 ≤ beta := hst.beta_pos.le
  have hb1 : beta < 1 := hst.beta_lt_one
  set C := pbar * (D + lam * pbar + gam * pbar) with hC
  have href_mem : ∀ m0 p0 (q : ℕ → Set.Icc (0 : ℝ) pbar) n, m0 ∈ Set.Icc (0 : ℝ) pbar →
      p0 ∈ Set.Icc (0 : ℝ) pbar →
      refPrice theta m0 p0 (fun n => (q n : ℝ)) n ∈ Set.Icc (0 : ℝ) pbar := by
    intro m0 p0 q n hm0 hp0
    have h1 := minPrice_mem pbar m0 (fun n => (q n : ℝ)) hm0 (fun n => (q n).2) n
    have h2 := price_mem pbar p0 (fun n => (q n : ℝ)) hp0 (fun n => (q n).2) n
    unfold refPrice
    constructor
    · nlinarith [mul_nonneg hth0 h1.1, mul_nonneg hth1 h2.1]
    · nlinarith [mul_le_mul_of_nonneg_left h1.2 hth0, mul_le_mul_of_nonneg_left h2.2 hth1]
  have hterm : ∀ m0 p0 (q : ℕ → Set.Icc (0 : ℝ) pbar) n, m0 ∈ Set.Icc (0 : ℝ) pbar →
      p0 ∈ Set.Icc (0 : ℝ) pbar →
      ‖beta ^ n * profit d0 lam gam (q n) (refPrice theta m0 p0 (fun n => (q n : ℝ)) n)‖ ≤
        C * beta ^ n := by
    intro m0 p0 q n hm0 hp0
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hb0 n), mul_comm]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hb0 n)
    exact profit_bound pbar D d0 lam gam _ _ hlam hgam (q n).2 (href_mem m0 p0 q n hm0 hp0)
      (hst.assumption1.nonneg _ (q n).2) (hD ⟨_, (q n).2, rfl⟩)
  have hgeo : Summable (fun n : ℕ => C * beta ^ n) :=
    (summable_geometric_of_lt_one hb0 hb1).mul_left C
  have hsum : ∀ m0 p0 (q : ℕ → Set.Icc (0 : ℝ) pbar), m0 ∈ Set.Icc (0 : ℝ) pbar →
      p0 ∈ Set.Icc (0 : ℝ) pbar → Summable (fun n =>
        beta ^ n * profit d0 lam gam (q n) (refPrice theta m0 p0 (fun n => (q n : ℝ)) n)) :=
    fun m0 p0 q hm0 hp0 => Summable.of_norm_bounded hgeo (fun n => hterm m0 p0 q n hm0 hp0)
  have hbdd : ∀ m0 p0, m0 ∈ Set.Icc (0 : ℝ) pbar → p0 ∈ Set.Icc (0 : ℝ) pbar →
      BddAbove (Set.range (fun q : ℕ → Set.Icc (0 : ℝ) pbar =>
        pathValue d0 lam gam theta beta m0 p0 (fun n => (q n : ℝ)))) := by
    intro m0 p0 hm0 hp0
    refine ⟨∑' n, C * beta ^ n, ?_⟩
    rintro _ ⟨q, rfl⟩
    unfold pathValue
    exact Summable.tsum_le_tsum (fun n => (le_abs_self _).trans
      (by rw [← Real.norm_eq_abs]; exact hterm m0 p0 q n hm0 hp0)) (hsum m0 p0 q hm0 hp0) hgeo
  have hmonoJ : ∀ m0 p0 m0' p0', m0 ∈ Set.Icc (0 : ℝ) pbar → p0 ∈ Set.Icc (0 : ℝ) pbar →
      m0' ∈ Set.Icc (0 : ℝ) pbar → p0' ∈ Set.Icc (0 : ℝ) pbar → m0 ≤ m0' → p0 ≤ p0' →
      J pbar d0 lam gam theta beta m0 p0 ≤ J pbar d0 lam gam theta beta m0' p0' := by
    intro m0 p0 m0' p0' hm0 hp0 hm0' hp0' hm hp
    unfold J
    apply ciSup_mono (hbdd m0' p0' hm0' hp0')
    intro q
    unfold pathValue
    apply Summable.tsum_le_tsum _ (hsum m0 p0 q hm0 hp0) (hsum m0' p0' q hm0' hp0')
    intro n
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hb0 n)
    apply profit_mono d0 lam gam _ _ _ hlam hgam (q n).2.1
    unfold refPrice
    have h1 := minPrice_mono m0 m0' (fun n => (q n : ℝ)) hm n
    have h2 := price_mono p0 p0' (fun n => (q n : ℝ)) hp n
    nlinarith [mul_le_mul_of_nonneg_left h1 hth0, mul_le_mul_of_nonneg_left h2 hth1]
  constructor
  · intro m m' p hm hm' hp hmm
    exact hmonoJ m p m' p hm hp hm' hp hmm le_rfl
  · intro m p p' hm hp hp' hpp
    exact hmonoJ m p m p' hm hp hm hp' le_rfl hpp
