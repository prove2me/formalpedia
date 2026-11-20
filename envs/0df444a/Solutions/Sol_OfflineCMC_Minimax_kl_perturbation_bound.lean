-- Prove2me | solution 1 for OfflineCMC.Minimax.kl_perturbation_bound
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:14:37.396072+00:00
-- url     : https://prove2.me/submissions/22959a4d-4344-443b-8c75-7c4e320cf7ed

import Mathlib
import Definitions.Def_OfflineCMC_Minimax_CMC
import Definitions.Def_OfflineCMC_Minimax_HardFamily

open OfflineCMC.Minimax Finset

/-- pairing: sums over `2k` split into consecutive pairs -/
lemma sum_range_pairs (F : ℕ → ℝ) (k : ℕ) :
    ∑ n ∈ range (2 * k), F n = ∑ i ∈ range k, (F (2 * i) + F (2 * i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

lemma hardSign_sum (d : ℕ) (hd : Even d) (σ : Fin (d / 2) → ℤˣ) :
    ∑ t : Fin (d + 1), hardSign σ t = 0 := by
  classical
  let F : ℕ → ℝ := fun n => if h : n / 2 < d / 2 then
    (if n % 2 = 0 then (1 : ℝ) else -1) * (((σ ⟨n / 2, h⟩ : ℤˣ) : ℤ) : ℝ) else 0
  have hF : ∀ t : Fin (d + 1), hardSign σ t = F t.val := fun t => rfl
  simp_rw [hF]
  rw [Fin.sum_univ_eq_sum_range F (d + 1), sum_range_succ]
  obtain ⟨k, rfl⟩ := hd
  have hk : (k + k) / 2 = k := by omega
  have hlast : F (k + k) = 0 := by simp [F, hk]
  rw [hlast, add_zero, show k + k = 2 * k by ring, sum_range_pairs]
  refine sum_eq_zero (fun i hi => ?_)
  have hi' : i < k := mem_range.mp hi
  have hA : (2 * i) / 2 < (k + k) / 2 := by omega
  have hB : (2 * i + 1) / 2 < (k + k) / 2 := by omega
  simp only [F, dif_pos hA, dif_pos hB]
  have hσ : σ ⟨(2 * i + 1) / 2, hB⟩ = σ ⟨(2 * i) / 2, hA⟩ := by
    congr 1; ext; simp only; omega
  have m1 : (2 * i) % 2 = 0 := by omega
  have m2 : (2 * i + 1) % 2 = 1 := by omega
  rw [hσ, m1, m2]; norm_num

lemma hardSign_sq_le (d : ℕ) (σ : Fin (d / 2) → ℤˣ) (t : Fin (d + 1)) : hardSign σ t ^ 2 ≤ 1 := by
  unfold hardSign
  split_ifs with h h2
  · rcases Int.units_eq_one_or (σ ⟨t.val / 2, h⟩) with e | e <;> simp [e]
  · rcases Int.units_eq_one_or (σ ⟨t.val / 2, h⟩) with e | e <;> simp [e]
  · norm_num

lemma hardSign_last (d : ℕ) (σ : Fin (d / 2) → ℤˣ) : hardSign σ (Fin.last d) = 0 := by
  unfold hardSign; simp

theorem solution (d : ℕ) (hd : Even d) (hd0 : 0 < d) (p ε : ℝ) (hp : 0 < p)
    (hpd : p < 1 / ((d : ℝ) + 1)) (hε : 0 < ε) (hε' : ε < 1 / 32) (σ : Fin (d / 2) → ℤˣ) :
    klDivFin (etaRow d p ε σ) (baseRow d p) ≤ 256 * ε ^ 2 / (1 - p) ∧
      256 * ε ^ 2 / (1 - p) ≤ 512 * ε ^ 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hd2 : (2 : ℝ) ≤ d := by
    obtain ⟨k, rfl⟩ := hd; have : 1 ≤ k := by omega
    push_cast; have : (1 : ℝ) ≤ k := by exact_mod_cast this
    linarith
  have hp1 : p < 1 / 3 := by
    have : 1 / ((d : ℝ) + 1) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have h1p : 1 / 2 ≤ 1 - p := by linarith
  refine ⟨?_, ?_⟩
  · set η := etaRow d p ε σ with hη
    set b := baseRow d p with hb
    have hbpos : ∀ t, 0 < b t := by
      intro t; simp only [hb, baseRow]; split_ifs
      · exact hp
      · exact div_pos (by linarith) hdR
    have hdiff : ∀ t, η t - b t = 16 * ε * hardSign σ t / d := by
      intro t
      by_cases ht : t = Fin.last d
      · subst ht; simp [hη, hb, etaRow, baseRow, hardSign_last]
      · simp only [hη, hb, etaRow, baseRow, if_neg ht]; ring
    have hηnn : ∀ t, 0 ≤ η t := by
      intro t
      have hs := hardSign_sq_le d σ t
      have habs : |hardSign σ t| ≤ 1 := by
        rw [← sq_le_one_iff_abs_le_one]; exact hs
      have := hdiff t
      have hb := hbpos t
      by_cases ht : t = Fin.last d
      · subst ht; show 0 ≤ etaRow d p ε σ (Fin.last d); simp [etaRow]; exact hp.le
      · have hbt : b t = (1 - p) / d := by show baseRow d p t = _; simp [baseRow, ht]
        rw [show η t = b t + 16 * ε * hardSign σ t / d by linarith, hbt, ← add_div]
        refine div_nonneg ?_ hdR.le
        have : -1 ≤ hardSign σ t := (abs_le.mp habs).1
        nlinarith
    -- per-term inequality
    have hterm : ∀ t, η t * Real.log (η t / b t) ≤ (η t - b t) + (η t - b t) ^ 2 / b t := by
      intro t
      have hb := hbpos t
      rcases (hηnn t).eq_or_lt with h0 | hpos
      · rw [← h0]
        have e : (0 - b t) + (0 - b t) ^ 2 / b t = 0 := by field_simp; ring
        rw [e]; simp
      · have hl := Real.log_le_sub_one_of_pos (div_pos hpos hb)
        have e : η t * (η t / b t - 1) = (η t - b t) + (η t - b t) ^ 2 / b t := by
          field_simp; ring
        rw [← e]; exact mul_le_mul_of_nonneg_left hl hpos.le
    unfold klDivFin
    refine (sum_le_sum (fun t _ => hterm t)).trans ?_
    rw [sum_add_distrib]
    have hsum0 : ∑ t, (η t - b t) = 0 := by
      simp_rw [hdiff, ← sum_div, ← mul_sum, hardSign_sum d hd σ]; simp
    rw [hsum0, zero_add, Fin.sum_univ_castSucc]
    have hlastsq : (η (Fin.last d) - b (Fin.last d)) ^ 2 / b (Fin.last d) = 0 := by
      rw [hdiff, hardSign_last]; simp
    rw [hlastsq, add_zero]
    have hle : ∀ i : Fin d, (η i.castSucc - b i.castSucc) ^ 2 / b i.castSucc
        ≤ 256 * ε ^ 2 / (d * (1 - p)) := by
      intro i
      have hne : i.castSucc ≠ Fin.last d := Fin.castSucc_ne_last i
      have hbt : b i.castSucc = (1 - p) / d := by show baseRow d p _ = _; simp [baseRow, hne]
      rw [hdiff, hbt]
      have hs := hardSign_sq_le d σ i.castSucc
      have h1p' : 0 < 1 - p := by linarith
      rw [show (16 * ε * hardSign σ i.castSucc / d) ^ 2 / ((1 - p) / d)
          = 256 * ε ^ 2 * hardSign σ i.castSucc ^ 2 / (d * (1 - p)) by field_simp; ring]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      nlinarith [sq_nonneg ε]
    calc ∑ i : Fin d, (η i.castSucc - b i.castSucc) ^ 2 / b i.castSucc
        ≤ ∑ _i : Fin d, 256 * ε ^ 2 / (d * (1 - p)) := sum_le_sum (fun i _ => hle i)
      _ = 256 * ε ^ 2 / (1 - p) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  · rw [div_le_iff₀ (by linarith)]; nlinarith [sq_nonneg ε]
