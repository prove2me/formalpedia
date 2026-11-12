-- Prove2me | solution 1 for RiskBalancingMNL.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T00:40:19.875551+00:00
-- url     : https://prove2.me/submissions/d99d7dcc-7903-4785-9ec2-9061a6124843

import Mathlib
import Definitions.Def_RiskBalancingMNL_Params
import Definitions.Def_RiskBalancingMNL_mHat
import Theorems.Thm_RiskBalancingMNL_markup_share_inverse

open RiskBalancingMNL

theorem solution {n : ℕ} (P : Params n) (lam : ℝ) (hlam0 : 0 ≤ lam) (_hlam1 : lam < 1) :
    (∀ m : Fin n → ℝ, Feasible P m → (¬ ∃ t : ℝ, m = constM t) →
      ∃ t : ℝ, 0 ≤ t ∧ objective P lam m < objective P lam (constM t)) ∧
    (∀ m : Fin n → ℝ, IsOptimal P lam m → ∃ t : ℝ, m = constM t) := by
  have hpart1 : ∀ m : Fin n → ℝ, Feasible P m → (¬ ∃ t : ℝ, m = constM t) →
      ∃ t : ℝ, 0 ≤ t ∧ objective P lam m < objective P lam (constM t) := by
    intro m hfeas hnot
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · exfalso
      refine hnot ⟨0, ?_⟩
      ext i
      exact i.elim0
    have : NeZero n := ⟨hn_pos.ne'⟩
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn_pos
    obtain ⟨i_any⟩ := ‹Nonempty (Fin n)›
    obtain ⟨hm_all, hmHat_inv, _, _⟩ := markup_share_inverse P
    obtain ⟨hq_pos, hq0_pos, hsum1, _, hm_recover⟩ := hm_all m
    let q : Fin n → ℝ := share P m
    let q0 : ℝ := noPurchase P m
    let S : ℝ := ∑ i, q i
    let π : ℝ := profit P m
    let g : ℝ := spread P m
    have hπ_nonneg : 0 ≤ π := hfeas
    have hS_pos : 0 < S :=
      (hq_pos i_any).trans_le
        (Finset.single_le_sum (f := q) (fun i _ => (hq_pos i).le) (Finset.mem_univ i_any))
    have hq0_lt1 : q0 < 1 := by
      change noPurchase P m < 1
      linarith
    let V : ℝ := ∑ i, q i * (S * m i - π) ^ 2
    have hV_id : V = S * (S * g - π ^ 2) := by
      have hexp : ∀ i : Fin n,
          q i * (S * m i - π) ^ 2 =
            S ^ 2 * (m i ^ 2 * q i) - 2 * S * π * (m i * q i) + π ^ 2 * q i := by
        intro i
        ring
      dsimp [V]
      simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      change S ^ 2 * g - 2 * S * π * π + π ^ 2 * S = S * (S * g - π ^ 2)
      ring
    have hex_ne : ∃ i₀ : Fin n, S * m i₀ - π ≠ 0 := by
      by_contra hall
      push Not at hall
      refine hnot ⟨π / S, ?_⟩
      ext i
      dsimp [constM]
      have hi := hall i
      exact eq_div_of_mul_eq hS_pos.ne' (by linarith)
    obtain ⟨i₀, hi₀_ne⟩ := hex_ne
    have hV_pos : 0 < V :=
      (mul_pos (hq_pos i₀) (sq_pos_of_ne_zero hi₀_ne)).trans_le
        (Finset.single_le_sum (f := fun i => q i * (S * m i - π) ^ 2)
          (fun i _ => mul_nonneg (hq_pos i).le (sq_nonneg _)) (Finset.mem_univ i₀))
    have hcs_strict : π ^ 2 < S * g := by
      by_contra hle
      have : V ≤ 0 := by
        rw [hV_id]
        nlinarith [hS_pos]
      linarith
    by_cases hSlam : S ≤ lam
    · have hg_pos : 0 < g := by
        by_contra hle
        have : S * g ≤ 0 := by nlinarith [hS_pos]
        nlinarith [sq_nonneg π]
      have hobj_neg : objective P lam m < 0 := by
        change π ^ 2 - lam * g < 0
        nlinarith
      have hobj0 : objective P lam (constM 0) = 0 := by
        unfold objective profit spread constM
        simp
      exact ⟨0, le_rfl, by linarith⟩
    · have hlam_lt_S : lam < S := lt_of_not_ge hSlam
      let t : ℝ := mHat P q0
      have hq0_t : noPurchase P (constM t) = q0 := hmHat_inv q0 hq0_pos hq0_lt1
      obtain ⟨hq'_pos, _, hsum1', _, ht_recover⟩ := hm_all (constM t)
      let q' : Fin n → ℝ := share P (constM t)
      have hS' : ∑ i, q' i = S := by
        change ∑ i, share P (constM t) i = ∑ i, share P m i
        linarith
      have hdiff : ∀ i : Fin n, P.b * (t - m i) = -Real.log (q' i / q i) := by
        intro i
        have hm_i := hm_recover i
        have ht_i := ht_recover i
        change m i = (P.a i + Real.log q0 - Real.log (q i)) / P.b - P.c i at hm_i
        change t = (P.a i + Real.log (noPurchase P (constM t)) - Real.log (q' i)) / P.b - P.c i
          at ht_i
        rw [hq0_t] at ht_i
        rw [Real.log_div (hq'_pos i).ne' (hq_pos i).ne']
        have hb_ne : P.b ≠ 0 := P.hb.ne'
        have hsub : t - m i = (Real.log (q i) - Real.log (q' i)) / P.b := by
          rw [ht_i, hm_i]
          ring
        rw [hsub, mul_div_cancel₀ _ hb_ne]
        ring
      have hex_qne : ∃ i₁ : Fin n, q' i₁ / q i₁ ≠ 1 := by
        by_contra hall
        push Not at hall
        refine hnot ⟨t, ?_⟩
        ext i
        dsimp [constM]
        have hlog0 : Real.log (q' i / q i) = 0 := by rw [hall i, Real.log_one]
        have hb_diff := hdiff i
        rw [hlog0, neg_zero] at hb_diff
        have htm : t - m i = 0 := (mul_eq_zero.mp hb_diff).resolve_left P.hb.ne'
        linarith
      obtain ⟨i₁, hi₁_ne⟩ := hex_qne
      have hkl_le : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          q i * Real.log (q' i / q i) ≤ q' i - q i := by
        intro i _
        have hle := Real.log_le_sub_one_of_pos (div_pos (hq'_pos i) (hq_pos i))
        have hmul := mul_le_mul_of_nonneg_left hle (hq_pos i).le
        have hsimp : q i * (q' i / q i - 1) = q' i - q i := by
          rw [mul_sub, mul_div_cancel₀ _ (hq_pos i).ne', mul_one]
        dsimp only [q, q'] at hsimp ⊢
        linarith
      have hkl_lt_i1 : q i₁ * Real.log (q' i₁ / q i₁) < q' i₁ - q i₁ := by
        have hlt := Real.log_lt_sub_one_of_pos (div_pos (hq'_pos i₁) (hq_pos i₁)) hi₁_ne
        have hmul := mul_lt_mul_of_pos_left hlt (hq_pos i₁)
        have hsimp : q i₁ * (q' i₁ / q i₁ - 1) = q' i₁ - q i₁ := by
          rw [mul_sub, mul_div_cancel₀ _ (hq_pos i₁).ne', mul_one]
        dsimp only [q, q'] at hsimp ⊢
        linarith
      have hkl_neg : ∑ i, q i * Real.log (q' i / q i) < 0 := by
        have hlt := Finset.sum_lt_sum hkl_le ⟨i₁, Finset.mem_univ i₁, hkl_lt_i1⟩
        rw [Finset.sum_sub_distrib, hS', sub_self] at hlt
        exact hlt
      have hb_profit : P.b * (t * S - π) = -∑ i, q i * Real.log (q' i / q i) := by
        have h1 : t * S - π = ∑ i, q i * (t - m i) := by
          dsimp [S, π, profit, q]
          simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
          congr 1
          · ring
          · refine Finset.sum_congr rfl fun i _ => ?_
            ring
        rw [h1, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hi := hdiff i
        calc P.b * (q i * (t - m i))
            = q i * (P.b * (t - m i)) := by ring
          _ = -(q i * Real.log (q' i / q i)) := by rw [hi]; ring
      have hπ_lt_tS : π < t * S := by
        by_contra hle
        have : P.b * (t * S - π) ≤ 0 := by nlinarith [P.hb]
        linarith
      have ht_pos : 0 < t := by
        by_contra hle
        have : t * S ≤ 0 := by nlinarith [hS_pos]
        linarith
      have hobj_t : objective P lam (constM t) = t ^ 2 * S * (S - lam) := by
        unfold objective profit spread constM
        simp_rw [← Finset.mul_sum]
        change (t * ∑ i, q' i) ^ 2 - lam * (t ^ 2 * ∑ i, q' i) = t ^ 2 * S * (S - lam)
        rw [hS']
        ring
      have hS_obj : S * objective P lam m < S * objective P lam (constM t) := by
        rw [hobj_t]
        change S * (π ^ 2 - lam * g) < S * (t ^ 2 * S * (S - lam))
        have h1 : S * (π ^ 2 - lam * g) ≤ π ^ 2 * (S - lam) := by
          have : lam * π ^ 2 ≤ lam * (S * g) := mul_le_mul_of_nonneg_left hcs_strict.le hlam0
          linarith
        have h2 : π ^ 2 < (t * S) ^ 2 := by nlinarith
        have h3 : π ^ 2 * (S - lam) < (t * S) ^ 2 * (S - lam) :=
          mul_lt_mul_of_pos_right h2 (by linarith)
        have h4 : (t * S) ^ 2 * (S - lam) = S * (t ^ 2 * S * (S - lam)) := by ring
        linarith
      have hlt_obj : objective P lam m < objective P lam (constM t) := by
        by_contra hle
        have : S * objective P lam (constM t) ≤ S * objective P lam m :=
          mul_le_mul_of_nonneg_left (not_lt.mp hle) hS_pos.le
        linarith
      exact ⟨t, ht_pos.le, hlt_obj⟩
  refine ⟨hpart1, fun m hopt => ?_⟩
  by_contra hnot
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · refine hnot ⟨0, ?_⟩
    ext i
    exact i.elim0
  have : NeZero n := ⟨hn_pos.ne'⟩
  obtain ⟨t, ht_nonneg, hlt⟩ := hpart1 m hopt.1 hnot
  obtain ⟨hm_all, _, _, _⟩ := markup_share_inverse P
  have hq'_pos := (hm_all (constM t)).1
  have hfeas_t : Feasible P (constM t) :=
    Finset.sum_nonneg fun i _ => mul_nonneg ht_nonneg (hq'_pos i).le
  exact hlt.not_ge (hopt.2 (constM t) hfeas_t)
