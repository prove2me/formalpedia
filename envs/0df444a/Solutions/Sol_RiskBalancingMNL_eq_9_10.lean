-- Prove2me | solution 1 for RiskBalancingMNL.eq_9_10
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T00:40:20.581491+00:00
-- url     : https://prove2.me/submissions/647e49fe-23ab-453c-bf60-1f9e873f5be4

import Mathlib
import Definitions.Def_RiskBalancingMNL_Params
import Definitions.Def_RiskBalancingMNL_mHat
import Theorems.Thm_RiskBalancingMNL_markup_share_inverse

open RiskBalancingMNL

theorem solution {n : ℕ} [NeZero n] (P : Params n) :
    (∀ lam t : ℝ,
      objective P lam (constM t) =
        (t * ∑ i, share P (constM t) i) ^ 2 - lam * t ^ 2 * ∑ i, share P (constM t) i ∧
      (t * ∑ i, share P (constM t) i) ^ 2 - lam * t ^ 2 * ∑ i, share P (constM t) i =
        t ^ 2 * (∑ i, share P (constM t) i) * (∑ i, share P (constM t) i - lam) ∧
      t ^ 2 * (∑ i, share P (constM t) i) * (∑ i, share P (constM t) i - lam) =
        t ^ 2 * (1 - noPurchase P (constM t)) * (1 - noPurchase P (constM t) - lam)) ∧
    (∀ t : ℝ, Feasible P (constM t) ↔ 0 ≤ t) ∧
    (∀ lam : ℝ, 0 ≤ lam → lam < lamBar P → ∀ m : Fin n → ℝ, IsOptimal P lam m →
      noPurchase P m < 1 - lam) := by
  obtain ⟨hm_all, hmHat_inv, hmHat_left, hmHat_mono⟩ := markup_share_inverse P
  have hpart1 : ∀ lam t : ℝ,
      objective P lam (constM t) =
        (t * ∑ i, share P (constM t) i) ^ 2 - lam * t ^ 2 * ∑ i, share P (constM t) i ∧
      (t * ∑ i, share P (constM t) i) ^ 2 - lam * t ^ 2 * ∑ i, share P (constM t) i =
        t ^ 2 * (∑ i, share P (constM t) i) * (∑ i, share P (constM t) i - lam) ∧
      t ^ 2 * (∑ i, share P (constM t) i) * (∑ i, share P (constM t) i - lam) =
        t ^ 2 * (1 - noPurchase P (constM t)) * (1 - noPurchase P (constM t) - lam) := by
    intro lam t
    refine ⟨?_, by ring, ?_⟩
    · unfold objective profit spread constM
      simp_rw [← Finset.mul_sum]
      ring
    · have hsum := (hm_all (constM t)).2.2.1
      have hS : ∑ i, share P (constM t) i = 1 - noPurchase P (constM t) := by linarith
      rw [hS]
  have hpart2 : ∀ t : ℝ, Feasible P (constM t) ↔ 0 ≤ t := by
    intro t
    have hlhs : Feasible P (constM t) ↔ 0 ≤ t * ∑ i, share P (constM t) i := by
      unfold Feasible profit
      simp_rw [show ∀ i : Fin n, constM t i = t from fun _ => rfl, ← Finset.mul_sum]
    rw [hlhs]
    have hq_pos := (hm_all (constM t)).1
    have hS_pos : 0 < ∑ i, share P (constM t) i :=
      (hq_pos 0).trans_le
        (Finset.single_le_sum (fun i _ => (hq_pos i).le) (Finset.mem_univ (0 : Fin n)))
    constructor
    · intro h
      by_contra hlt
      have : t * ∑ i, share P (constM t) i < 0 :=
        mul_neg_of_neg_of_pos (lt_of_not_ge hlt) hS_pos
      linarith
    · intro h
      exact mul_nonneg h hS_pos.le
  refine ⟨hpart1, hpart2, fun lam hlam0 hlam m hopt => ?_⟩
  have hZ_pos : 0 < zeroMarkupMass P :=
    (Real.exp_pos _).trans_le
      (Finset.single_le_sum (f := fun i => Real.exp (P.a i - P.b * P.c i))
        (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ (0 : Fin n)))
  have hq0_zero : noPurchase P (constM 0) = 1 - lamBar P := by
    have hattr0 : ∑ j, attraction P (constM 0) j = zeroMarkupMass P := by
      unfold attraction constM zeroMarkupMass
      refine Finset.sum_congr rfl fun j _ => ?_
      ring_nf
    unfold noPurchase lamBar
    rw [hattr0]
    have hden : 1 + zeroMarkupMass P ≠ 0 := by linarith
    field_simp [hden]
    ring
  have hlamBar_lt1 : lamBar P < 1 := by
    unfold lamBar
    rw [div_lt_one (by linarith)]
    linarith
  have h1_sub_pos : 0 < 1 - lamBar P := by linarith
  let x₁ : ℝ := ((1 - lamBar P) + (1 - lam)) / 2
  have hx1_gt : 1 - lamBar P < x₁ := by dsimp [x₁]; linarith
  have hx1_lt : x₁ < 1 - lam := by dsimp [x₁]; linarith
  have hx1_mem : x₁ ∈ Set.Ioo 0 1 := ⟨by linarith, by linarith⟩
  have h0_mem : 1 - lamBar P ∈ Set.Ioo 0 1 := ⟨h1_sub_pos, by linarith [
    (div_pos hZ_pos (by linarith : 0 < 1 + zeroMarkupMass P) : 0 < lamBar P)]⟩
  have hm0 : mHat P (1 - lamBar P) = 0 := by
    rw [← hq0_zero]
    exact hmHat_left 0
  let t₁ : ℝ := mHat P x₁
  have ht1_pos : 0 < t₁ := by
    dsimp [t₁]
    rw [← hm0]
    exact hmHat_mono h0_mem hx1_mem hx1_gt
  have hq0_t1 : noPurchase P (constM t₁) = x₁ := hmHat_inv x₁ hx1_mem.1 hx1_mem.2
  have hobj_t1_pos : 0 < objective P lam (constM t₁) := by
    obtain ⟨h1, h2, h3⟩ := hpart1 lam t₁
    rw [h1, h2, h3, hq0_t1]
    exact mul_pos (mul_pos (sq_pos_of_pos ht1_pos) (by linarith)) (by linarith)
  have hfeas_t1 : Feasible P (constM t₁) := (hpart2 t₁).mpr ht1_pos.le
  have hobj_m_pos : 0 < objective P lam m := hobj_t1_pos.trans_le (hopt.2 (constM t₁) hfeas_t1)
  by_contra hge
  have hq0_ge : 1 - lam ≤ noPurchase P m := not_lt.mp hge
  obtain ⟨hq_pos, _, hsum1, _, _⟩ := hm_all m
  let q : Fin n → ℝ := share P m
  let S : ℝ := ∑ i, q i
  let π : ℝ := profit P m
  let g : ℝ := spread P m
  have hS_le_lam : S ≤ lam := by
    change ∑ i, share P m i ≤ lam
    linarith
  have hS_pos : 0 < S :=
    (hq_pos 0).trans_le (Finset.single_le_sum (fun i _ => (hq_pos i).le) (Finset.mem_univ 0))
  have hg_nonneg : 0 ≤ g :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hq_pos i).le
  have hV_nonneg : 0 ≤ ∑ i, q i * (S * m i - π) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hq_pos i).le (sq_nonneg _)
  have hV_id : (∑ i, q i * (S * m i - π) ^ 2) = S * (S * g - π ^ 2) := by
    have hexp : ∀ i : Fin n,
        q i * (S * m i - π) ^ 2 =
          S ^ 2 * (m i ^ 2 * q i) - 2 * S * π * (m i * q i) + π ^ 2 * q i := by
      intro i
      ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    change S ^ 2 * g - 2 * S * π * π + π ^ 2 * S = S * (S * g - π ^ 2)
    ring
  have hcs : π ^ 2 ≤ S * g := by
    by_contra hlt
    have : S * (S * g - π ^ 2) < 0 := mul_neg_of_pos_of_neg hS_pos (by linarith)
    linarith
  have hobj_nonpos : objective P lam m ≤ 0 := by
    change π ^ 2 - lam * g ≤ 0
    have : S * g ≤ lam * g := mul_le_mul_of_nonneg_right hS_le_lam hg_nonneg
    linarith
  linarith
