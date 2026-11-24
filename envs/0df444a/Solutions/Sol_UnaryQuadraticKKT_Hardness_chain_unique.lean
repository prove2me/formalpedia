-- Prove2me | solution 1 for UnaryQuadraticKKT.Hardness.chain_unique
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T16:46:44.044424+00:00
-- url     : https://prove2.me/submissions/751e9181-9a14-4524-86fb-105bea9fe22f

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Chain

set_option autoImplicit false

open UnaryQuadraticKKT.Hardness NetworkEquilibriumCLS.LinearNash

namespace ChainUniqueAux

/-- Adjacent differences `2 w_i - w_{i+1}`. -/
def D {k : ℕ} (w : Fin (k + 2) → ℝ) (i : Fin (k + 1)) : ℝ :=
  2 * w ⟨i.val, by omega⟩ - w ⟨i.val + 1, by omega⟩

/-- The bilinear form of the quadratic part of the chain objective. -/
def B {k : ℕ} (d w : Fin (k + 2) → ℝ) : ℝ :=
  3 * ∑ i : Fin (k + 1), D d i * D w i + 9 * d ⟨k + 1, by omega⟩ * w ⟨k + 1, by omega⟩

/-- Standard basis vector. -/
def e {k : ℕ} (j : Fin (k + 2)) : Fin (k + 2) → ℝ := fun m => if j = m then 1 else 0

lemma D_add {k : ℕ} (w w' : Fin (k + 2) → ℝ) (i : Fin (k + 1)) :
    D (w + w') i = D w i + D w' i := by
  simp only [D, Pi.add_apply]; ring

lemma D_smul {k : ℕ} (c : ℝ) (w : Fin (k + 2) → ℝ) (i : Fin (k + 1)) :
    D (c • w) i = c * D w i := by
  simp only [D, Pi.smul_apply, smul_eq_mul]; ring

lemma D_sub {k : ℕ} (w w' : Fin (k + 2) → ℝ) (i : Fin (k + 1)) :
    D (w - w') i = D w i - D w' i := by
  simp only [D, Pi.sub_apply]; ring

/-- `B d` as a linear map. -/
def Blin {k : ℕ} (d : Fin (k + 2) → ℝ) : (Fin (k + 2) → ℝ) →ₗ[ℝ] ℝ where
  toFun w := B d w
  map_add' w w' := by
    simp only [B, D_add, mul_add, Finset.sum_add_distrib, Pi.add_apply]; ring
  map_smul' c w := by
    simp only [B, D_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have : ∑ i : Fin (k + 1), D d i * (c * D w i) = c * ∑ i : Fin (k + 1), D d i * D w i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [this]; ring

lemma B_lin_sum {k : ℕ} (d w : Fin (k + 2) → ℝ) :
    ∑ j, w j * B d (e j) = B d w := by
  have h := LinearMap.pi_apply_eq_sum_univ (Blin d) w
  simp only [smul_eq_mul] at h
  exact h.symm

lemma B_nonneg {k : ℕ} (d : Fin (k + 2) → ℝ) : 0 ≤ B d d := by
  have : 0 ≤ ∑ i : Fin (k + 1), D d i * D d i :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h2 := mul_self_nonneg (d ⟨k + 1, by omega⟩)
  simp only [B]; nlinarith

lemma B_eq_zero {k : ℕ} (d : Fin (k + 2) → ℝ) (h : B d d = 0) : d = 0 := by
  have hs0 : 0 ≤ ∑ i : Fin (k + 1), D d i * D d i :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hl0 := mul_self_nonneg (d ⟨k + 1, by omega⟩)
  simp only [B] at h
  have hs : ∑ i : Fin (k + 1), D d i * D d i = 0 := by nlinarith
  have hl : d ⟨k + 1, by omega⟩ = 0 := mul_self_eq_zero.mp (by nlinarith)
  have hD : ∀ i, D d i = 0 := fun i =>
    mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg _).mp hs i
      (Finset.mem_univ _))
  have key : ∀ m : ℕ, ∀ j (hj : j < k + 2), j + m = k + 1 → d ⟨j, hj⟩ = 0 := by
    intro m
    induction m with
    | zero =>
      intro j hj hjm
      have : j = k + 1 := by omega
      subst this; exact hl
    | succ m ih =>
      intro j hj hjm
      have h1 := hD ⟨j, by omega⟩
      have h2 := ih (j + 1) (by omega) (by omega)
      simp only [D] at h1
      linarith
  funext i
  exact key (k + 1 - i.val) i.val i.isLt (by omega)

lemma B_add {k : ℕ} (d w : Fin (k + 2) → ℝ) (h : ℝ) :
    B (d + h • w) (d + h • w) = B d d + 2 * h * B d w + h ^ 2 * B w w := by
  have hD : ∀ i, D (d + h • w) i = D d i + h * D w i := fun i => by
    rw [D_add, D_smul]
  simp only [B, hD, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have : ∑ i : Fin (k + 1), (D d i + h * D w i) * (D d i + h * D w i) =
      ∑ i : Fin (k + 1), D d i * D d i + 2 * h * ∑ i : Fin (k + 1), D d i * D w i +
        h ^ 2 * ∑ i : Fin (k + 1), D w i * D w i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [this]; ring

lemma update_eq {k : ℕ} (u : Fin (k + 2) → ℝ) (j : Fin (k + 2)) (t : ℝ) :
    Function.update u j t = u + (t - u j) • e j := by
  funext m
  by_cases h : m = j
  · subst h; simp [e]
  · have h' : ¬ j = m := fun h'' => h h''.symm
    simp [Function.update_apply, e, h, h']

/-- Telescoping. -/
lemma telescope {k : ℕ} (w : Fin (k + 2) → ℝ) :
    ∑ i : Fin (k + 1), D w i * (1 / 2 : ℝ) ^ (i.val + 1) =
      w ⟨0, by omega⟩ - (1 / 2 : ℝ) ^ (k + 1) * w ⟨k + 1, by omega⟩ := by
  set W : ℕ → ℝ := fun j => if h : j < k + 2 then w ⟨j, h⟩ else 0 with hW
  have hr : ∀ m : ℕ, ∑ i ∈ Finset.range m, (2 * W i - W (i + 1)) * (1 / 2 : ℝ) ^ (i + 1) =
      W 0 - (1 / 2 : ℝ) ^ m * W m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  have hc : ∑ i : Fin (k + 1), D w i * (1 / 2 : ℝ) ^ (i.val + 1) =
      ∑ i : Fin (k + 1), (2 * W i.val - W (i.val + 1)) * (1 / 2 : ℝ) ^ (i.val + 1) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [D, hW, dif_pos (show (i : ℕ) < k + 2 by omega),
      dif_pos (show (i : ℕ) + 1 < k + 2 by omega)]
  rw [hc, Fin.sum_univ_eq_sum_range (fun i => (2 * W i - W (i + 1)) * (1 / 2 : ℝ) ^ (i + 1)) (k + 1),
    hr]
  simp [hW]

end ChainUniqueAux

open ChainUniqueAux

theorem solution (k : ℕ) (hk : 1 ≤ k) (s : ℤ) (hs : s = -1 ∨ s = 1)
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    ChainGlobalMin k s x y (chainMinimizer k s x y) ∧
    (∀ u, ChainGlobalMin k s x y u → u = chainMinimizer k s x y) ∧
    IntervalKKT (fun _ => -1) (fun _ => 1) (chainValue k s x y)
      (chainMinimizer k s x y) ∧
    (∀ u, IntervalKKT (fun _ => -1) (fun _ => 1) (chainValue k s x y) u →
      u = chainMinimizer k s x y) := by
  set us := chainMinimizer k s x y with hus
  set f := chainValue k s x y with hf
  -- interior of the cube (Lemma 4.4)
  have hint : ∀ i : Fin (k + 2), -1 < us i ∧ us i < 1 := by
    intro i
    have hi : i.val ≤ k + 1 := by omega
    set a : ℝ := (2 : ℝ) ^ (-(i.val : ℤ)) with ha
    set b : ℝ := (2 : ℝ) ^ ((i.val : ℤ) + 1 - ((k : ℤ) + 2)) with hb
    have ha0 : 0 < a := zpow_pos (by norm_num) _
    have hb0 : 0 < b := zpow_pos (by norm_num) _
    have ha1 : a ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    have hb1 : b ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    have hxa : a * x ≤ 1 := by nlinarith
    have hyb : b * y ≤ 1 := by nlinarith
    have hxa0 : 0 ≤ a * x := by nlinarith
    have hyb0 : 0 ≤ b * y := by nlinarith
    simp only [hus, chainMinimizer]
    rw [← ha, ← hb]
    rcases hs with rfl | rfl <;> push_cast <;> constructor <;> nlinarith
  -- adjacent differences of the minimizer
  have hc : ∀ i : Fin (k + 1), D us i = (1 / 2 : ℝ) ^ (i.val + 1) * x := by
    intro i
    simp only [D, hus, chainMinimizer]
    have h1 : (2 : ℝ) ^ (-((i.val + 1 : ℕ) : ℤ)) = (2 : ℝ) ^ (-(i.val : ℤ) - 1) := by
      congr 1; push_cast; ring
    have h2 : (2 : ℝ) ^ (((i.val + 1 : ℕ) : ℤ) + 1 - ((k : ℤ) + 2))
        = 2 * (2 : ℝ) ^ ((i.val : ℤ) + 1 - ((k : ℤ) + 2)) := by
      rw [show (((i.val + 1 : ℕ) : ℤ) + 1 - ((k : ℤ) + 2)) = ((i.val : ℤ) + 1 - ((k : ℤ) + 2)) + 1 by
        push_cast; ring, zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    have h3 : (2 : ℝ) ^ (-(i.val : ℤ)) = 2 * (2 : ℝ) ^ (-(i.val : ℤ) - 1) := by
      rw [show (-(i.val : ℤ)) = (-(i.val : ℤ) - 1) + 1 by ring,
        zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring_nf
    have h4 : (2 : ℝ) ^ (-(i.val : ℤ) - 1) = (1 / 2 : ℝ) ^ (i.val + 1) := by
      rw [show (-(i.val : ℤ) - 1) = -((i.val + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
        zpow_natCast, one_div, inv_pow]
    rw [h1, h2, h3, h4]
    ring
  -- last coordinate of the minimizer
  have hlast : us ⟨k + 1, by omega⟩ = ((1 / 2 : ℝ) ^ (k + 1) * x - (s : ℝ) * y) / 3 := by
    simp only [hus, chainMinimizer]
    rw [show (((k + 1 : ℕ) : ℤ) + 1 - ((k : ℤ) + 2)) = 0 by push_cast; ring, zpow_zero,
      zpow_neg, zpow_natCast, one_div, inv_pow]
    ring
  -- the objective is the quadratic form centred at the minimizer, plus a constant
  have hval : ∀ w : Fin (k + 2) → ℝ,
      f w = 3 * ∑ i : Fin (k + 1), D w i * D w i + 9 * w ⟨k + 1, by omega⟩ ^ 2 -
        6 * x * w ⟨0, by omega⟩ + 6 * (s : ℝ) * y * w ⟨k + 1, by omega⟩ + x ^ 2 + y ^ 2 := by
    intro w
    simp only [hf, chainValue, D, sq]
  have hF1 : ∀ v, f v = B (v - us) (v - us) + f us := by
    intro v
    have T1 := telescope v
    have T2 := telescope us
    have hS2 : ∑ i : Fin (k + 1), D v i * D us i =
        x * (v ⟨0, by omega⟩ - (1 / 2 : ℝ) ^ (k + 1) * v ⟨k + 1, by omega⟩) := by
      rw [← T1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hc]; ring
    have hS3 : ∑ i : Fin (k + 1), D us i * D us i =
        x * (us ⟨0, by omega⟩ - (1 / 2 : ℝ) ^ (k + 1) * us ⟨k + 1, by omega⟩) := by
      rw [← T2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hc i]; ring
    have hexp : ∑ i : Fin (k + 1), D (v - us) i * D (v - us) i =
        ∑ i : Fin (k + 1), D v i * D v i - 2 * ∑ i : Fin (k + 1), D v i * D us i +
          ∑ i : Fin (k + 1), D us i * D us i := by
      simp only [D_sub]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hval v, hval us]
    simp only [B, hexp, Pi.sub_apply]
    rw [hS2, hS3, hlast]
    ring
  -- coordinate partials
  have hpart : ∀ (u : Fin (k + 2) → ℝ) (j : Fin (k + 2)),
      coordinatePartial f u j = 2 * B (u - us) (e j) := by
    intro u j
    set d := u - us with hd
    have hg : (fun t => f (Function.update u j t)) = fun t =>
        (f us + B d d) + (2 * B d (e j)) * (t - u j) + B (e j) (e j) * (t - u j) ^ 2 := by
      funext t
      rw [hF1, update_eq, show u + (t - u j) • e j - us = d + (t - u j) • e j by
        rw [hd]; abel, B_add]
      ring
    have h1 : HasDerivAt (fun t : ℝ => t - u j) 1 (u j) := (hasDerivAt_id _).sub_const _
    have h2 := ((h1.const_mul (2 * B d (e j))).const_add (f us + B d d)).add
      ((h1.pow 2).const_mul (B (e j) (e j)))
    simp only [coordinatePartial]
    rw [hg]
    exact (h2.congr_deriv (by simp)).deriv
  have hB0 : ∀ j : Fin (k + 2), B (0 : Fin (k + 2) → ℝ) (e j) = 0 := by
    intro j; simp [B, D]
  refine ⟨⟨fun i => ⟨(hint i).1.le, (hint i).2.le⟩, fun v _ => ?_⟩, fun u hu => ?_, ?_, fun u hu => ?_⟩
  · change f us ≤ f v
    rw [hF1 v]; linarith [B_nonneg (v - us)]
  · have h := hu.2 us (fun i => ⟨(hint i).1.le, (hint i).2.le⟩)
    change f u ≤ f us at h
    rw [hF1 u] at h
    have := B_eq_zero (u - us) (le_antisymm (by linarith) (B_nonneg _))
    exact sub_eq_zero.mp this
  · refine ⟨fun i => ⟨(hint i).1.le, (hint i).2.le⟩, fun i => ?_⟩
    rw [hpart, sub_self, hB0]
    simp
  · set d := u - us with hd
    have hterm : ∀ j, 0 ≤ (us j - u j) * B d (e j) := by
      intro j
      have hp := hpart u j
      rcases lt_trichotomy (u j) (us j) with h | h | h
      · have := (hu.2 j).2 (by linarith [(hint j).2])
        rw [hp] at this
        exact mul_nonneg (by linarith) (by linarith)
      · rw [h, sub_self, zero_mul]
      · have := (hu.2 j).1 (by linarith [(hint j).1])
        rw [hp] at this
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    have hsum : ∑ j, (us j - u j) * B d (e j) = -B d d := by
      rw [← B_lin_sum d d, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hd, Pi.sub_apply]; ring
    have h0 : 0 ≤ ∑ j, (us j - u j) * B d (e j) := Finset.sum_nonneg fun j _ => hterm j
    have := B_eq_zero d (le_antisymm (by linarith) (B_nonneg d))
    exact sub_eq_zero.mp this
