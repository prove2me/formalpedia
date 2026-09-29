-- Prove2me | solution 1 for Weinberg1965.fWeinberg_expansion
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T03:46:21.886166+00:00
-- url     : https://prove2.me/submissions/5bdf8f9c-88bc-4c51-99d9-f04371d2a159

import Mathlib
import Definitions.Def_Weinberg1965_Defs

open Asymptotics
open Weinberg1965

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem W6_Weinberg1965_suffix : ∀ (N : ℕ) (z : Fin N → ℂ),
    (∀ s : Finset (Fin N), s.Nonempty → ∑ i ∈ s, z i ≠ 0) →
    ∑ σ : Equiv.Perm (Fin N),
        ∏ k : Fin N, (∑ j ∈ Finset.univ.filter (fun j : Fin N => k ≤ j), z (σ j))⁻¹
      = ∏ i : Fin N, (z i)⁻¹
  | 0, z, hz => by simp
  | N + 1, z, hz => by
    have hshift : ∀ (f : Fin (N + 1) → ℂ) (k : Fin N),
        ∑ j ∈ Finset.univ.filter (fun j : Fin (N + 1) => k.succ ≤ j), f j =
          ∑ j ∈ Finset.univ.filter (fun j : Fin N => k ≤ j), f j.succ := by
      intro f k
      rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
      have h0 : ¬ (k.succ ≤ (0 : Fin (N + 1))) := by
        rw [not_le]; exact Fin.succ_pos k
      simp only [h0, if_false, zero_add, Fin.succ_le_succ_iff]
    set T := ∑ j, z j with hTdef
    have htot : ∀ σ : Equiv.Perm (Fin (N + 1)),
        ∑ j ∈ Finset.univ.filter (fun j : Fin (N + 1) => (0 : Fin (N + 1)) ≤ j), z (σ j) = T := by
      intro σ
      rw [Finset.sum_filter]
      simp only [Fin.zero_le, if_true]
      exact Equiv.sum_comp σ z
    have hT : T ≠ 0 := hz Finset.univ Finset.univ_nonempty
    have hzi : ∀ i, z i ≠ 0 := fun i => by
      simpa using hz {i} (Finset.singleton_nonempty i)
    have hz' : ∀ p : Fin (N + 1), ∀ s : Finset (Fin N), s.Nonempty →
        ∑ i ∈ s, z (Equiv.swap 0 p i.succ) ≠ 0 := by
      intro p s hs
      let e : Fin N ↪ Fin (N + 1) :=
        ⟨fun i => Equiv.swap 0 p i.succ, fun a b h => Fin.succ_injective _ ((Equiv.swap 0 p).injective h)⟩
      have : ∑ i ∈ s, z (Equiv.swap 0 p i.succ) = ∑ j ∈ s.map e, z j := by
        rw [Finset.sum_map]; rfl
      rw [this]
      exact hz _ (hs.map)
    have key : ∀ p : Fin (N + 1),
        ∏ k : Fin N, (z (Equiv.swap 0 p k.succ))⁻¹ = z p * ∏ i, (z i)⁻¹ := by
      intro p
      have h1 : ∏ i, (z i)⁻¹ = ∏ i, (z (Equiv.swap 0 p i))⁻¹ :=
        (Equiv.prod_comp (Equiv.swap 0 p) (fun i => (z i)⁻¹)).symm
      rw [h1, Fin.prod_univ_succ, Equiv.swap_apply_left, ← mul_assoc, mul_inv_cancel₀ (hzi p),
        one_mul]
    calc ∑ σ : Equiv.Perm (Fin (N + 1)),
          ∏ k : Fin (N + 1), (∑ j ∈ Finset.univ.filter (fun j : Fin (N + 1) => k ≤ j), z (σ j))⁻¹
        = ∑ σ : Equiv.Perm (Fin (N + 1)), T⁻¹ *
            ∏ k : Fin N, (∑ j ∈ Finset.univ.filter (fun j : Fin N => k ≤ j), z (σ j.succ))⁻¹ := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [Fin.prod_univ_succ, htot]
          congr 1
          refine Finset.prod_congr rfl fun k _ => ?_
          rw [hshift (fun j => z (σ j))]
      _ = ∑ pe : Fin (N + 1) × Equiv.Perm (Fin N), T⁻¹ *
            ∏ k : Fin N, (∑ j ∈ Finset.univ.filter (fun j : Fin N => k ≤ j),
              z (Equiv.Perm.decomposeFin.symm pe j.succ))⁻¹ :=
          (Equiv.sum_comp Equiv.Perm.decomposeFin.symm
            (fun σ : Equiv.Perm (Fin (N + 1)) => T⁻¹ *
              ∏ k : Fin N, (∑ j ∈ Finset.univ.filter (fun j : Fin N => k ≤ j),
                z (σ j.succ))⁻¹)).symm
      _ = ∑ p : Fin (N + 1), ∑ e : Equiv.Perm (Fin N), T⁻¹ *
            ∏ k : Fin N, (∑ j ∈ Finset.univ.filter (fun j : Fin N => k ≤ j),
              z (Equiv.swap 0 p (e j).succ))⁻¹ := by
          rw [Fintype.sum_prod_type]
          simp only [Equiv.Perm.decomposeFin_symm_apply_succ]
      _ = ∑ p : Fin (N + 1), T⁻¹ * ∏ k : Fin N, (z (Equiv.swap 0 p k.succ))⁻¹ := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← Finset.mul_sum]
          congr 1
          exact W6_Weinberg1965_suffix N (fun k => z (Equiv.swap 0 p k.succ)) (hz' p)
      _ = ∑ p : Fin (N + 1), T⁻¹ * (z p * ∏ i, (z i)⁻¹) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [key p]
      _ = ∏ i : Fin (N + 1), (z i)⁻¹ := by
          rw [← Finset.mul_sum, ← Finset.sum_mul, ← hTdef, ← mul_assoc, inv_mul_cancel₀ hT,
            one_mul]

theorem W6_Weinberg1965_soft_factor_factorization (N : ℕ) (z : Fin N → ℂ)
    (hz : ∀ s : Finset (Fin N), s.Nonempty → ∑ i ∈ s, z i ≠ 0) :
    ∑ σ : Equiv.Perm (Fin N),
        ∏ k : Fin N, (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ≤ k), z (σ j))⁻¹
      = ∏ i : Fin N, (z i)⁻¹ := by
  rw [← W6_Weinberg1965_suffix N z hz]
  have hper : ∀ σ : Equiv.Perm (Fin N),
      ∏ k : Fin N, (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ≤ k), z (σ j))⁻¹ =
        ∏ k : Fin N, (∑ j ∈ Finset.univ.filter (fun j : Fin N => k ≤ j),
          z (((σ * Fin.revPerm : Equiv.Perm (Fin N))) j))⁻¹ := by
    intro σ
    rw [← Equiv.prod_comp Fin.revPerm]
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    rw [Finset.sum_filter, Finset.sum_filter, ← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Fin.revPerm_apply, Fin.rev_le_rev, Equiv.Perm.mul_apply]
  simp_rw [hper]
  exact Equiv.sum_comp (Equiv.mulRight Fin.revPerm)
    (fun τ : Equiv.Perm (Fin N) => ∏ k : Fin N,
      (∑ j ∈ Finset.univ.filter (fun j : Fin N => k ≤ j), z (τ j))⁻¹)

set_option maxHeartbeats 1000000 in
theorem solution :
    (fun β : ℝ => fWeinberg β - (1 + 11 / 6 * β ^ 2 + 63 / 40 * β ^ 4)) =O[nhds 0]
      (fun β : ℝ => β ^ 6) := by
  apply Asymptotics.IsBigO.of_bound 100
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with b hb
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  rcases eq_or_ne b 0 with rfl | hb0
  · simp [fWeinberg]
  have hab := abs_nonneg b
  have hb1 : |b| < 1 := by linarith
  have hbsq : b ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]; nlinarith
  have hS : ∀ x : ℝ, (∑ i ∈ Finset.range 6, x ^ (i + 1) / ((i : ℝ) + 1)) =
      x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 + x ^ 6 / 6 := by
    intro x
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    try ring
  have e1 := Real.abs_log_sub_add_sum_range_le hb1 6
  have hnb : |-b| < 1 := by rwa [abs_neg]
  have e2 := Real.abs_log_sub_add_sum_range_le hnb 6
  rw [hS] at e1 e2
  rw [abs_neg] at e2
  have hb7 : |b| ^ (6 + 1) / (1 - |b|) ≤ 2 * |b| ^ 7 := by
    have h7 : 0 ≤ |b| ^ 7 := by positivity
    have hpos : 0 < 1 - |b| := by linarith
    rw [div_le_iff₀ hpos, show (6 : ℕ) + 1 = 7 from rfl]
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ 1 - |b| by linarith) h7
    linarith
  set X1 := b + b ^ 2 / 2 + b ^ 3 / 3 + b ^ 4 / 4 + b ^ 5 / 5 + b ^ 6 / 6 + Real.log (1 - b)
    with hX1
  set X2 := -b + (-b) ^ 2 / 2 + (-b) ^ 3 / 3 + (-b) ^ 4 / 4 + (-b) ^ 5 / 5 + (-b) ^ 6 / 6 +
    Real.log (1 - -b) with hX2
  set E := X2 - X1 with hE
  have hEb : |E| ≤ 4 * |b| ^ 7 := by
    calc |E| = |X2 - X1| := rfl
      _ ≤ |X2| + |X1| := abs_sub _ _
      _ ≤ 2 * |b| ^ 7 + 2 * |b| ^ 7 := add_le_add (e2.trans hb7) (e1.trans hb7)
      _ = 4 * |b| ^ 7 := by ring
  have h1b : 0 < 1 + b := by linarith [(abs_lt.1 (show |b| < 1 / 2 from hb)).1]
  have h1b' : 0 < 1 - b := by linarith [(abs_lt.1 (show |b| < 1 / 2 from hb)).2]
  have hL : Real.log ((1 + b) / (1 - b)) = 2 * b * (1 + b ^ 2 / 3 + b ^ 4 / 5) + E := by
    rw [Real.log_div h1b.ne' h1b'.ne', hE, hX1, hX2]
    have : (1 : ℝ) - -b = 1 + b := by ring
    rw [this]
    ring
  set s := Real.sqrt (1 - b ^ 2) with hs
  have hs2 : s ^ 2 = 1 - b ^ 2 := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs_ge : 1 / 2 ≤ s := by
    have e : (1 / 2 : ℝ) = Real.sqrt ((1 / 2) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    rw [e, hs]
    exact Real.sqrt_le_sqrt (by linarith [hbsq, show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num])
  have hspos : 0 < s := by linarith
  set Q := (1 + b ^ 2) * (1 + b ^ 2 / 3 + b ^ 4 / 5) with hQ
  set P := 1 + 11 / 6 * b ^ 2 + 63 / 40 * b ^ 4 with hP
  have hQ1 : 1 ≤ Q := by
    have h0 : 0 ≤ b ^ 2 * (4 / 3 + 8 / 15 * b ^ 2 + b ^ 4 / 5) := by positivity
    have h1 : Q - 1 = b ^ 2 * (4 / 3 + 8 / 15 * b ^ 2 + b ^ 4 / 5) := by rw [hQ]; ring
    linarith
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hD : 1 ≤ Q + s * P := by have := mul_nonneg hs0 hP0; linarith
  set c := 307 / 120 + 11843 / 2880 * b ^ 2 + 12931 / 4800 * b ^ 4 + b ^ 6 / 25 with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hc10 : c ≤ 10 := by
    rw [hc]
    have h4 : b ^ 4 ≤ 1 / 16 := by
      calc b ^ 4 = (b ^ 2) ^ 2 := by ring
        _ ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ (sq_nonneg b) hbsq 2
        _ = 1 / 16 := by norm_num
    have h6 : b ^ 6 ≤ 1 / 64 := by
      calc b ^ 6 = (b ^ 2) ^ 3 := by ring
        _ ≤ (1 / 4) ^ 3 := pow_le_pow_left₀ (sq_nonneg b) hbsq 3
        _ = 1 / 64 := by norm_num
    linarith
  have hR : Q ^ 2 - s ^ 2 * P ^ 2 = b ^ 6 * c := by
    rw [hs2, hQ, hP, hc]; ring
  have hf : fWeinberg b = Q / s + (1 + b ^ 2) * E / (2 * b * s) := by
    unfold fWeinberg
    rw [if_neg hb0, hL, ← hs, hQ]
    field_simp
    try ring
  have h2 : Q / s - P = (Q ^ 2 - s ^ 2 * P ^ 2) / ((Q + s * P) * s) := by
    field_simp
    ring
  have hsplit : fWeinberg b - (1 + 11 / 6 * b ^ 2 + 63 / 40 * b ^ 4) =
      b ^ 6 * c / ((Q + s * P) * s) + (1 + b ^ 2) * E / (2 * b * s) := by
    rw [hf, ← hP, ← hR, ← h2]; ring
  have hDs : 0 < (Q + s * P) * s := mul_pos (by linarith) hspos
  have hb6 : 0 ≤ |b| ^ 6 := by positivity
  have t1 : |b ^ 6 * c / ((Q + s * P) * s)| ≤ 20 * |b| ^ 6 := by
    rw [abs_div, abs_of_pos hDs, div_le_iff₀ hDs, abs_mul, abs_of_nonneg hc0, abs_pow]
    have hDs2 : 1 / 2 ≤ (Q + s * P) * s := by
      have := mul_le_mul hD hs_ge (by norm_num) (by linarith)
      linarith
    calc |b| ^ 6 * c ≤ |b| ^ 6 * 10 := mul_le_mul_of_nonneg_left hc10 hb6
      _ ≤ |b| ^ 6 * (20 * ((Q + s * P) * s)) := mul_le_mul_of_nonneg_left (by linarith) hb6
      _ = 20 * |b| ^ 6 * ((Q + s * P) * s) := by ring
  have hbpos : 0 < |b| := abs_pos.2 hb0
  have t2 : |(1 + b ^ 2) * E / (2 * b * s)| ≤ 5 * |b| ^ 6 := by
    have hden : 0 < |2 * b * s| := by positivity
    rw [abs_div, div_le_iff₀ hden, abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos hspos,
      abs_of_pos (by positivity : (0 : ℝ) < 1 + b ^ 2)]
    calc (1 + b ^ 2) * |E| ≤ (5 / 4) * (4 * |b| ^ 7) :=
          mul_le_mul (by linarith) hEb (abs_nonneg _) (by norm_num)
      _ = 5 * |b| ^ 6 * |b| := by ring
      _ ≤ 5 * |b| ^ 6 * (2 * |b| * s) :=
          mul_le_mul_of_nonneg_left (by
            have h2 : |b| * 1 ≤ |b| * (2 * s) := mul_le_mul_of_nonneg_left (by linarith) hab
            linarith) (by positivity)
  rw [hsplit, abs_pow]
  calc |b ^ 6 * c / ((Q + s * P) * s) + (1 + b ^ 2) * E / (2 * b * s)|
      ≤ |b ^ 6 * c / ((Q + s * P) * s)| + |(1 + b ^ 2) * E / (2 * b * s)| := abs_add_le _ _
    _ ≤ 20 * |b| ^ 6 + 5 * |b| ^ 6 := add_le_add t1 t2
    _ ≤ 100 * |b| ^ 6 := by linarith
