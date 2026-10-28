-- Prove2me | solution 2 for Pegasos.Analysis.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:48:20.964008+00:00
-- url     : https://prove2.me/submissions/0eabcae6-6c8e-476a-b73b-febedb1e16dc

import Mathlib
import Definitions.Def_Pegasos_Analysis_Model
import Theorems.Thm_Pegasos_Analysis_lemma_1
import Theorems.Thm_Pegasos_Analysis_subgrad_bound_no_projection
import Theorems.Thm_Pegasos_Analysis_wstar_norm_bound

-- carved verbatim out of submission c6566800-4fea-4877-ab3b-0f187c5d74ab, lines 507-573

section
set_option autoImplicit false
open Pegasos.Analysis
open scoped InnerProductSpace

lemma quad_ineq {n : ℕ} (lam : ℝ) (hlam : 0 ≤ lam) (u w : EuclideanSpace ℝ (Fin n)) :
    lam / 2 * ‖w‖ ^ 2 + lam * inner ℝ (u - w) w ≤ lam / 2 * ‖u‖ ^ 2 := by
  have h := norm_add_sq_real w (u - w)
  rw [add_sub_cancel] at h
  rw [h, real_inner_comm]
  nlinarith [mul_nonneg hlam (sq_nonneg ‖u - w‖)]

lemma hinge_sub {n : ℕ} (w u x : EuclideanSpace ℝ (Fin n)) (y : ℝ) :
    UnderstandingML.hingeLoss w (x, y)
      + (if y * inner ℝ w x < 1 then -(y * inner ℝ (u - w) x) else 0)
      ≤ UnderstandingML.hingeLoss u (x, y) := by
  unfold UnderstandingML.hingeLoss
  simp only
  split_ifs with h
  · rw [max_eq_right (by linarith), inner_sub_left]
    have := le_max_right 0 (1 - y * inner ℝ u x)
    linarith
  · rw [max_eq_left (by linarith)]
    simp

lemma R_nonneg {n m k : ℕ} (hk : 0 < k) (R : ℝ) (x : Fin m → EuclideanSpace ℝ (Fin n))
    (hR : ∀ i, ‖x i‖ ≤ R) (B : Fin k → Fin m) : 0 ≤ R :=
  le_trans (norm_nonneg _) (hR (B ⟨0, hk⟩))

lemma hingeTerm_norm {n m k : ℕ} (hk : 0 < k) (R : ℝ) (x : Fin m → EuclideanSpace ℝ (Fin n))
    (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) (hR : ∀ i, ‖x i‖ ≤ R) (B : Fin k → Fin m)
    (w : EuclideanSpace ℝ (Fin n)) : ‖hingeTerm x y B w‖ ≤ R := by
  have hR0 := R_nonneg hk R x hR B
  unfold hingeTerm
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hs : ‖∑ j, (if y (B j) * inner ℝ w (x (B j)) < 1 then y (B j) • x (B j) else 0)‖ ≤ k * R := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖(if y (B j) * inner ℝ w (x (B j)) < 1 then y (B j) • x (B j) else 0)‖
        ≤ ∑ _j : Fin k, R := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          split_ifs
          · rw [norm_smul, Real.norm_eq_abs]
            rcases hy (B j) with h | h <;> simp [h, hR (B j)]
          · simpa using hR0
      _ = k * R := by simp
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  calc 1 / (k : ℝ) * ‖∑ j, (if y (B j) * inner ℝ w (x (B j)) < 1 then y (B j) • x (B j) else 0)‖
      ≤ 1 / (k : ℝ) * (k * R) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = R := by field_simp

lemma projBall_norm_le {n : ℕ} (lam : ℝ) (hlam : 0 < lam) (v : EuclideanSpace ℝ (Fin n)) :
    ‖projBall lam v‖ ≤ 1 / Real.sqrt lam := by
  have hr : 0 < 1 / Real.sqrt lam := by positivity
  unfold projBall
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (by positivity))]
  by_cases hv : ‖v‖ = 0
  · rw [hv]; simpa using hr.le
  · calc min 1 (1 / Real.sqrt lam / ‖v‖) * ‖v‖ ≤ (1 / Real.sqrt lam / ‖v‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
      _ = 1 / Real.sqrt lam := div_mul_cancel₀ _ hv

theorem eq8 {n m k : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (x : Fin m → EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) (B : Fin k → Fin m)
    (w : EuclideanSpace ℝ (Fin n)) :
    UnderstandingML.IsSubgradient (instObj lam x y B) w (subgrad lam x y B w) := by
  intro u
  have hq := quad_ineq lam hlam.le u w
  have hk : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have hsum : ∑ j, (UnderstandingML.hingeLoss w (x (B j), y (B j))
        + (if y (B j) * inner ℝ w (x (B j)) < 1 then -(y (B j) * inner ℝ (u - w) (x (B j))) else 0))
      ≤ ∑ j, UnderstandingML.hingeLoss u (x (B j), y (B j)) :=
    Finset.sum_le_sum (fun j _ => hinge_sub w u (x (B j)) (y (B j)))
  have hinner : inner ℝ (u - w) (hingeTerm x y B w)
      = (1 / (k : ℝ)) * ∑ j, (if y (B j) * inner ℝ w (x (B j)) < 1 then
          y (B j) * inner ℝ (u - w) (x (B j)) else 0) := by
    unfold hingeTerm
    rw [inner_smul_right, inner_sum]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> simp [inner_smul_right]
  unfold instObj subgrad
  rw [inner_sub_right, inner_smul_right, hinner]
  rw [Finset.sum_add_distrib] at hsum
  have hneg : ∑ j, (if y (B j) * inner ℝ w (x (B j)) < 1 then -(y (B j) * inner ℝ (u - w) (x (B j))) else 0)
      = - ∑ j, (if y (B j) * inner ℝ w (x (B j)) < 1 then
          y (B j) * inner ℝ (u - w) (x (B j)) else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> simp
  rw [hneg] at hsum
  nlinarith [mul_le_mul_of_nonneg_left hsum hk]

lemma hinge_convex {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (y : ℝ) (u v : EuclideanSpace ℝ (Fin n))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    UnderstandingML.hingeLoss (a • u + b • v) (x, y) ≤
      a * UnderstandingML.hingeLoss u (x, y) + b * UnderstandingML.hingeLoss v (x, y) := by
  unfold UnderstandingML.hingeLoss
  simp only
  apply max_le
  · have h1 := le_max_left 0 (1 - y * inner ℝ u x)
    have h2 := le_max_left 0 (1 - y * inner ℝ v x)
    nlinarith [mul_nonneg ha h1, mul_nonneg hb h2]
  · have h1 := le_max_right 0 (1 - y * inner ℝ u x)
    have h2 := le_max_right 0 (1 - y * inner ℝ v x)
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [conj_trivial]
    have e : 1 - y * (a * inner ℝ u x + b * inner ℝ v x)
        = a * (1 - y * inner ℝ u x) + b * (1 - y * inner ℝ v x) := by
      have : (1 : ℝ) = a + b := hab.symm
      calc 1 - y * (a * inner ℝ u x + b * inner ℝ v x)
          = (a + b) * 1 - y * (a * inner ℝ u x + b * inner ℝ v x) := by rw [← this]; ring
        _ = _ := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

theorem instObj_sc {n m k : ℕ} (lam : ℝ)
    (x : Fin m → EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) (B : Fin k → Fin m) :
    ConvexOn ℝ Set.univ (fun w => instObj lam x y B w - lam / 2 * ‖w‖ ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  simp only [instObj, smul_eq_mul]
  have hk : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have hsum : ∑ j, UnderstandingML.hingeLoss (a • u + b • v) (x (B j), y (B j)) ≤
      a * ∑ j, UnderstandingML.hingeLoss u (x (B j), y (B j))
        + b * ∑ j, UnderstandingML.hingeLoss v (x (B j), y (B j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => hinge_convex _ _ u v a b ha hb hab)
  have := mul_le_mul_of_nonneg_left hsum hk
  nlinarith

theorem projBall_proj {n : ℕ} (lam : ℝ) (hlam : 0 < lam) (v : EuclideanSpace ℝ (Fin n)) :
    LogRegretOCO.OGD.IsProj (Metric.closedBall 0 (1 / Real.sqrt lam)) v (projBall lam v) := by
  have hr : 0 < 1 / Real.sqrt lam := by positivity
  set r := 1 / Real.sqrt lam with hrdef
  unfold projBall
  rw [← hrdef]
  by_cases hv : ‖v‖ ≤ r
  · have hz : min 1 (r / ‖v‖) • v = v := by
      by_cases hv0 : v = 0
      · simp [hv0]
      · have h1 : 1 ≤ r / ‖v‖ := (one_le_div (norm_pos_iff.2 hv0)).2 hv
        rw [min_eq_left h1, one_smul]
    rw [hz]
    refine ⟨by simpa using hv, fun w _ => by simp⟩
  · rw [not_le] at hv
    have hvpos : 0 < ‖v‖ := lt_trans hr hv
    have h1 : r / ‖v‖ < 1 := (div_lt_one hvpos).2 hv
    rw [min_eq_right h1.le]
    have hn : ‖(r / ‖v‖) • v‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hvpos)]
      field_simp
    refine ⟨by simp [hn], fun w hw => ?_⟩
    have hw' : ‖w‖ ≤ r := by simpa using hw
    have e : (r / ‖v‖) • v - v = (r / ‖v‖ - 1) • v := by rw [sub_smul, one_smul]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith)]
    have h2 : ‖v‖ - ‖w‖ ≤ ‖w - v‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le v w
    have h3 : -(r / ‖v‖ - 1) * ‖v‖ = ‖v‖ - r := by field_simp; ring
    rw [h3]
    linarith

theorem sg_proj {n m k : ℕ} (lam R : ℝ) (hlam : 0 < lam) (hk : 0 < k)
    (x : Fin m → EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hR : ∀ i, ‖x i‖ ≤ R) (A : ℕ → Fin k → Fin m) (t : ℕ) (ht : 1 ≤ t) :
    ‖run lam x y A true t‖ ≤ 1 / Real.sqrt lam ∧
      ‖subgrad lam x y (A t) (run lam x y A true t)‖ ≤ Real.sqrt lam + R := by
  have hr : 0 < 1 / Real.sqrt lam := by positivity
  have hw : ‖run lam x y A true t‖ ≤ 1 / Real.sqrt lam := by
    rcases Nat.eq_or_lt_of_le ht with h | h
    · subst h
      have : run lam x y A true 1 = 0 := rfl
      rw [this, norm_zero]; exact hr.le
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
      have e : run lam x y A true (s + 2) = projBall lam (run lam x y A true (s + 1)
          - (1 / (lam * ((s + 1 : ℕ) : ℝ))) • subgrad lam x y (A (s + 1)) (run lam x y A true (s + 1))) := rfl
      rw [e]
      exact projBall_norm_le lam hlam _
  refine ⟨hw, ?_⟩
  unfold subgrad
  calc ‖lam • run lam x y A true t - hingeTerm x y (A t) (run lam x y A true t)‖
      ≤ ‖lam • run lam x y A true t‖ + ‖hingeTerm x y (A t) (run lam x y A true t)‖ :=
        norm_sub_le _ _
    _ ≤ Real.sqrt lam + R := by
        refine add_le_add ?_ (hingeTerm_norm hk R x y hy hR _ _)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
        calc lam * ‖run lam x y A true t‖ ≤ lam * (1 / Real.sqrt lam) :=
              mul_le_mul_of_nonneg_left hw hlam.le
          _ = Real.sqrt lam := by
              have h := Real.sq_sqrt hlam.le
              have hs : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.2 hlam).ne'
              field_simp
              nlinarith [h]

theorem solution {n m k : ℕ} (lam R : ℝ) (hlam : 0 < lam) (hk : 0 < k)
    (x : Fin m → EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hR : ∀ i, ‖x i‖ ≤ R) (A : ℕ → Fin k → Fin m) (project : Bool)
    (wstar : EuclideanSpace ℝ (Fin n)) (hwstar : ∀ w, svmObj lam x y wstar ≤ svmObj lam x y w)
    (T : ℕ) (hT : 3 ≤ T) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, instObj lam x y (A t) (run lam x y A project t)
      ≤ (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, instObj lam x y (A t) wstar
        + (if project then (Real.sqrt lam + R) ^ 2 else 4 * R ^ 2) * (1 + Real.log T)
          / (2 * lam * T) := by
  have hr : 0 < 1 / Real.sqrt lam := by positivity
  have hws := Pegasos.Analysis.wstar_norm_bound lam hlam x y hy wstar hwstar
  have hR0 := R_nonneg hk R x hR (A 0)
  cases project with
  | true =>
    have := Pegasos.Analysis.lemma_1 lam (Real.sqrt lam + R) hlam (Metric.closedBall 0 (1 / Real.sqrt lam))
      Metric.isClosed_closedBall (convex_closedBall _ _) T
      (fun t => instObj lam x y (A t)) (fun t => run lam x y A true t)
      (fun t => subgrad lam x y (A t) (run lam x y A true t))
      (fun t _ => instObj_sc lam x y (A t))
      (by
        show run lam x y A true 1 ∈ _
        have h1t : run lam x y A true 1 = 0 := rfl
        rw [mem_closedBall_zero_iff, h1t, norm_zero]; exact hr.le)
      (by
        intro t ht
        have ht1 : 1 ≤ t := (Finset.mem_Icc.1 ht).1
        obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        exact projBall_proj lam hlam _)
      (fun t _ => eq8 lam hlam x y (A t) _)
      (fun t ht => (sg_proj lam R hlam hk x y hy hR A t (Finset.mem_Icc.1 ht).1).2)
      wstar (by simpa using hws)
    simpa using this
  | false =>
    have hρ : 0 < max (R / lam) (1 / Real.sqrt lam) := lt_max_of_lt_right hr
    have hmem : ∀ t : ℕ, 1 ≤ t → run lam x y A false (t + 1) ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (max (R / lam) (1 / Real.sqrt lam)) := by
      intro t ht
      rw [mem_closedBall_zero_iff]
      exact (Pegasos.Analysis.subgrad_bound_no_projection lam R hlam hk x y hy hR A t ht).1.trans (le_max_left _ _)
    have := Pegasos.Analysis.lemma_1 lam (2 * R) hlam (Metric.closedBall 0 (max (R / lam) (1 / Real.sqrt lam)))
      Metric.isClosed_closedBall (convex_closedBall _ _) T
      (fun t => instObj lam x y (A t)) (fun t => run lam x y A false t)
      (fun t => subgrad lam x y (A t) (run lam x y A false t))
      (fun t _ => instObj_sc lam x y (A t))
      (by
        show run lam x y A false 1 ∈ _
        have h1t : run lam x y A false 1 = 0 := rfl
        rw [mem_closedBall_zero_iff, h1t, norm_zero]; exact hρ.le)
      (by
        intro t ht
        have ht1 : 1 ≤ t := (Finset.mem_Icc.1 ht).1
        obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        have hm := hmem (s + 1) ht1
        have e : run lam x y A false (s + 1 + 1) = run lam x y A false (s + 1)
            - (1 / (lam * ((s + 1 : ℕ) : ℝ))) • subgrad lam x y (A (s + 1))
                (run lam x y A false (s + 1)) := rfl
        show LogRegretOCO.OGD.IsProj _ _ (run lam x y A false (s + 1 + 1))
        rw [e] at hm ⊢
        refine ⟨hm, fun w _ => ?_⟩
        simp)
      (fun t _ => eq8 lam hlam x y (A t) _)
      (fun t ht => (Pegasos.Analysis.subgrad_bound_no_projection lam R hlam hk x y hy hR A t (Finset.mem_Icc.1 ht).1).2)
      wstar (by rw [mem_closedBall_zero_iff]; exact hws.trans (le_max_right _ _))
    rw [show (2 * R) ^ 2 = 4 * R ^ 2 by ring] at this
    simp only [Bool.false_eq_true, if_false]
    simpa using this

end
