-- Prove2me | solution 1 for StationaryBwK.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:40:03.438204+00:00
-- url     : https://prove2.me/submissions/152db179-d7b8-46f0-afb7-3fc83df065fb

import Mathlib
import Definitions.Def_StationaryBwK_Benchmark
import Definitions.Def_StationaryBwK_StationarySeq

open StationaryBwK in
theorem solution {d K : ℕ} (T : ℕ) (B : ℝ) (hT : 1 ≤ T) (hB : 0 < B) (hBT : B ≤ T)
    (σr : ℝ) (hσr₀ : 0 ≤ σr) (hσr₁ : σr ≤ 1) (r : ℕ → Fin K → ℝ) (c : ℕ → Fin d → Fin K → ℝ)
    (hr : ∀ a : Fin K, IsStationarySeq σr T (fun t => r t a))
    (Ts : ℕ) (p : Fin K → ℝ) (hopt : IsOptFDSolution T B r c Ts p) :
    σr * ((1 - (Ts : ℝ) / T) / ((Ts : ℝ) / T)) * optFD T B r c ≤
      ∑ t ∈ Finset.Icc (Ts + 1) T, expect p (r t) := by
  obtain ⟨hTs, hp, hfeas, hmax⟩ := hopt
  have hopt' : optFD T B r c = fdValue r Ts p := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨Ts, hTs, p, hp, hfeas, rfl⟩, ?_⟩
    rintro _ ⟨Ts', h1, p', h2, h3, rfl⟩
    exact hmax Ts' h1 p' h2 h3
  have hTs1 := Finset.mem_Icc.mp hTs
  have key : ∀ s ∈ Finset.Icc 1 T, ∀ t ∈ Finset.Icc 1 T,
      σr * expect p (r s) ≤ expect p (r t) := by
    intro s hs t ht
    unfold expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    have h1 := hr a s hs t ht
    have hpa := hp.1 a
    calc σr * (p a * r s a) = p a * (σr * r s a) := by ring
      _ ≤ p a * r t a := mul_le_mul_of_nonneg_left h1 hpa
  have key2 : ∀ t ∈ Finset.Icc (Ts + 1) T, σr * fdValue r Ts p ≤ Ts * expect p (r t) := by
    intro t ht
    have ht' := Finset.mem_Icc.mp ht
    unfold fdValue
    rw [Finset.mul_sum]
    calc ∑ s ∈ Finset.Icc 1 Ts, σr * expect p (r s)
        ≤ ∑ s ∈ Finset.Icc 1 Ts, expect p (r t) := by
          apply Finset.sum_le_sum
          intro s hs
          have hs' := Finset.mem_Icc.mp hs
          exact key s (Finset.mem_Icc.mpr ⟨hs'.1, by omega⟩) t
            (Finset.mem_Icc.mpr ⟨by omega, ht'.2⟩)
      _ = Ts * expect p (r t) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          simp
  have hc : ((Finset.Icc (Ts + 1) T).card : ℝ) = (T : ℝ) - Ts := by
    rw [Nat.card_Icc, show T + 1 - (Ts + 1) = T - Ts by omega, Nat.cast_sub hTs1.2]
  have key3 := Finset.sum_le_sum key2
  rw [Finset.sum_const, nsmul_eq_mul, hc, ← Finset.mul_sum] at key3
  have hT0 : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hTspos : (0 : ℝ) < Ts := by exact_mod_cast hTs1.1
  have hf : (1 - (Ts : ℝ) / T) / ((Ts : ℝ) / T) = ((T : ℝ) - Ts) / Ts := by
    rw [one_sub_div hT0, div_div_div_cancel_right₀ hT0]
  rw [hopt', hf]
  rw [show σr * (((T : ℝ) - Ts) / Ts) * fdValue r Ts p =
      (σr * fdValue r Ts p * ((T : ℝ) - Ts)) / Ts by ring, div_le_iff₀ hTspos]
  linarith
