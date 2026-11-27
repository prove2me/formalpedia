-- Prove2me | solution 1 for SampleDrivenOS.Structure.Supplement.lemma_19
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:32.846861+00:00
-- url     : https://prove2.me/submissions/fe105276-a794-423c-9bde-5a552bdceabd

import Definitions.Def_SampleDrivenOS_Structure_Supplement_FiniteLP

open SampleDrivenOS
open SampleDrivenOS.Structure
open SampleDrivenOS.Structure.Supplement

theorem solution (N h k : ℕ) (p : ℝ) (hp : 0 < p ∧ p < 1)
    (hgrid : p = (h : ℝ) / (N : ℝ)) (hN : 1 / (1 - p) + 1 ≤ (N : ℝ))
    (hk : 1 ≤ k ∧ k ≤ h + 1) :
    1 ≤ cumulativeOffline N h k / (1 - p ^ k) ∧
    cumulativeOffline N h k / (1 - p ^ k) ≤
      1 + Real.exp 1 / ((1 - p) * ((N : ℝ) - 1)) := by
        obtain ⟨hp0, hp1⟩ := hp
        obtain ⟨hk1, hkh⟩ := hk
        have hNpos : (0:ℝ) < N := by
          rcases Nat.eq_zero_or_pos N with h0 | h0
          · subst h0; simp at hgrid; linarith
          · exact_mod_cast h0
        have hhN : (h:ℝ) < N := by
          have : (h:ℝ)/N < 1 := hgrid ▸ hp1
          rwa [div_lt_one hNpos] at this
        have h1p : 1 - p = ((N:ℝ) - h)/N := by rw [hgrid]; field_simp
        have hN2n : h + 2 ≤ N := by
          have hlt : h < N := by exact_mod_cast hhN
          have hne : h + 1 ≠ N := by
            intro heq
            have h1 : (N:ℝ) - h = 1 := by rw [← heq]; push_cast; ring
            rw [h1] at h1p
            have : 1/(1-p) = N := by rw [h1p]; field_simp
            linarith
          omega
        have hN2 : (h:ℝ) + 2 ≤ N := by exact_mod_cast hN2n
        have hh0 : (0:ℝ) ≤ h := h.cast_nonneg
        have hN1 : (0:ℝ) < N - 1 := by linarith
        set E := Real.exp 1 / ((1 - p) * ((N:ℝ) - 1)) with hE
        have hEid : (1-p) * E = Real.exp 1 / ((N:ℝ)-1) := by
          rw [hE]; field_simp [show (1 - p) ≠ 0 by linarith, hN1.ne']
        have hexp : ∀ k : ℕ, k ≤ N - 1 → ((N:ℝ)/((N:ℝ)-1))^k ≤ Real.exp 1 := by
          intro k hk
          have h1 : (N:ℝ)/((N:ℝ)-1) ≤ Real.exp (1/((N:ℝ)-1)) := by
            have := Real.add_one_le_exp (1/((N:ℝ)-1))
            have : (N:ℝ)/((N:ℝ)-1) = 1/((N:ℝ)-1) + 1 := by field_simp; ring
            linarith
          calc ((N:ℝ)/((N:ℝ)-1))^k ≤ (Real.exp (1/((N:ℝ)-1)))^k :=
                pow_le_pow_left₀ (div_pos hNpos hN1).le h1 k
            _ = Real.exp (k * (1/((N:ℝ)-1))) := by rw [← Real.exp_nat_mul]
            _ ≤ Real.exp 1 := by
              apply Real.exp_le_exp.mpr
              have : (k:ℝ) ≤ N - 1 := by
                have : (k:ℝ) ≤ ((N-1 : ℕ):ℝ) := by exact_mod_cast hk
                rw [Nat.cast_sub (by omega)] at this; simpa using this
              rw [mul_one_div, div_le_one hN1]; exact this
        set Q : ℕ → ℝ := fun k => ∏ s ∈ Finset.range k, ((h : ℝ) - s) / ((N : ℝ) - s) with hQ
        set R : ℕ → ℝ := fun k => ∏ s ∈ Finset.range k, ((h : ℝ) - s) / ((N : ℝ) - 1 - s) with hR
        have main : ∀ k : ℕ, k ≤ h + 1 →
            cumulativeOffline N h k = 1 - Q k ∧ Q k * N = R k * ((N:ℝ) - k) ∧ 0 ≤ Q k ∧
            Q k ≤ p^k ∧ 0 ≤ R k ∧ R k ≤ ((h:ℝ)/((N:ℝ)-1))^k ∧ p^k - Q k ≤ (1 - p^k) * E ∧
            (1-p)*k*p^k ≤ 1 - p^k := by
          intro k
          induction k with
          | zero => intro _; simp [cumulativeOffline, Q, R]
          | succ k ih =>
            intro hk
            obtain ⟨hC, hQR, hQ0, hQp, hR0, hRq, hD, hf⟩ := ih (by omega)
            have hkh : (k:ℝ) ≤ h := by exact_mod_cast (by omega : k ≤ h)
            have hk0 : (0:ℝ) ≤ k := k.cast_nonneg
            have hNk : (0:ℝ) < N - k := by linarith
            have hN1k : (0:ℝ) < N - 1 - k := by linarith
            have hQs : Q (k+1) = Q k * (((h:ℝ) - k)/((N:ℝ) - k)) := by
              simp only [hQ, Finset.prod_range_succ]
            have hRs : R (k+1) = R k * (((h:ℝ) - k)/((N:ℝ) - 1 - k)) := by
              simp only [hR, Finset.prod_range_succ]
            have hCs : cumulativeOffline N h (k+1) =
                cumulativeOffline N h k + ((N:ℝ)-h)/((N:ℝ)-k) * Q k := by
              unfold cumulativeOffline
              rw [Finset.sum_Icc_succ_top (by omega)]
              congr 1
              unfold offlineCoefficient
              simp only [Nat.add_sub_cancel, hQ]
              rw [show ((N:ℝ) - ((k+1:ℕ):ℝ) + 1) = (N:ℝ) - k by push_cast; ring]
            have hfac0 : 0 ≤ ((h:ℝ)-k)/((N:ℝ)-k) := div_nonneg (by linarith) hNk.le
            have hfac1 : ((h:ℝ)-k)/((N:ℝ)-k) ≤ p := by
              rw [hgrid, div_le_div_iff₀ hNk hNpos]; nlinarith
            have hfacR0 : 0 ≤ ((h:ℝ)-k)/((N:ℝ)-1-k) := div_nonneg (by linarith) hN1k.le
            have hfacR1 : ((h:ℝ)-k)/((N:ℝ)-1-k) ≤ h/((N:ℝ)-1) := by
              rw [div_le_div_iff₀ hN1k hN1]; nlinarith
            have hpk0 : 0 ≤ p^k := pow_nonneg hp0.le k
            have hpk1 : p^k ≤ 1 := pow_le_one₀ hp0.le hp1.le
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hCs, hC, hQs]; field_simp; ring
            · rw [hQs, hRs]; push_cast
              rw [show (N:ℝ) - ((k:ℝ) + 1) = (N:ℝ) - 1 - k by ring]
              calc Q k * (((h:ℝ) - k) / ((N:ℝ) - k)) * N = (Q k * N) * ((h:ℝ) - k) / ((N:ℝ) - k) := by ring
                _ = R k * ((h:ℝ) - k) := by rw [hQR]; field_simp
                _ = R k * (((h:ℝ) - k) / ((N:ℝ) - 1 - k)) * ((N:ℝ) - 1 - k) := by field_simp
            · rw [hQs]; exact mul_nonneg hQ0 hfac0
            · rw [hQs, pow_succ]; exact mul_le_mul hQp hfac1 hfac0 hpk0
            · rw [hRs]; exact mul_nonneg hR0 hfacR0
            · rw [hRs, pow_succ]; exact mul_le_mul hRq hfacR1 hfacR0 (pow_nonneg (div_nonneg hh0 hN1.le) _)
            · have hdiff : p - ((h:ℝ)-k)/((N:ℝ)-k) = (k:ℝ) * (1-p) / ((N:ℝ) - k) := by
                rw [hgrid]; field_simp; ring
              have hQk : Q k / ((N:ℝ) - k) = R k / N := by
                rw [div_eq_div_iff hNk.ne' hNpos.ne']; linarith
              have hRe : R k ≤ p^k * Real.exp 1 := by
                have : (h:ℝ)/((N:ℝ)-1) = p * ((N:ℝ)/((N:ℝ)-1)) := by
                  rw [hgrid]; field_simp
                rw [this, mul_pow] at hRq
                have := hexp k (by omega)
                calc R k ≤ _ := hRq
                  _ ≤ p^k * Real.exp 1 := mul_le_mul_of_nonneg_left this hpk0
              have hstep : Q k * (p - ((h:ℝ)-k)/((N:ℝ)-k)) = (1-p) * k * (R k / N) := by
                rw [hdiff, ← hQk]; ring
              have hb1 : (1-p) * k * p^k ≤ 1 := by linarith
              have hb2 : (1-p) * k * (R k / N) ≤ Real.exp 1 / ((N:ℝ)-1) := by
                have hRN : R k / N ≤ p^k * Real.exp 1 / N := div_le_div_of_nonneg_right hRe hNpos.le
                have h1p0 : 0 ≤ (1-p) * k := mul_nonneg (by linarith) hk0
                calc (1-p) * k * (R k / N) ≤ (1-p) * k * (p^k * Real.exp 1 / N) :=
                      mul_le_mul_of_nonneg_left hRN h1p0
                  _ = ((1-p) * k * p^k) * Real.exp 1 / N := by ring
                  _ ≤ 1 * Real.exp 1 / N := by
                      gcongr
                  _ ≤ Real.exp 1 / ((N:ℝ)-1) := by
                      rw [one_mul]; apply div_le_div_of_nonneg_left (Real.exp_pos 1).le hN1; linarith
              have : p^(k+1) - Q (k+1) = p * (p^k - Q k) + Q k * (p - ((h:ℝ)-k)/((N:ℝ)-k)) := by
                rw [hQs, pow_succ]; ring
              rw [this, hstep]
              have : (1 - p^(k+1)) * E = p * ((1 - p^k) * E) + (1-p) * E := by rw [pow_succ]; ring
              rw [this, hEid]
              have := mul_le_mul_of_nonneg_left hD hp0.le
              linarith
            · push_cast
              rw [pow_succ]
              have h1 := mul_le_mul_of_nonneg_left hf hp0.le
              have h2 : (1 - p) * (p^k * p) ≤ (1 - p) * 1 :=
                mul_le_mul_of_nonneg_left (mul_le_one₀ hpk1 hp0.le hp1.le) (by linarith)
              linarith
        obtain ⟨hC, -, -, hQp, -, -, hD, -⟩ := main k hkh
        have hpk : p^k < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
        have hden : 0 < 1 - p^k := by linarith
        rw [hC]
        constructor
        · rw [one_le_div hden]; linarith
        · rw [div_le_iff₀ hden]; linarith
