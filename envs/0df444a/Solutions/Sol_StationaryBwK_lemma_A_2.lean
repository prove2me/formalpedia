-- Prove2me | solution 1 for StationaryBwK.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:26:05.786907+00:00
-- url     : https://prove2.me/submissions/1d55eda7-47e4-4372-8292-99443643aea3

import Mathlib
import Definitions.Def_StationaryBwK_Benchmark
import Definitions.Def_StationaryBwK_StationarySeq

open StationaryBwK in
theorem solution {d K : ℕ} (T : ℕ) (B : ℝ) (hT : 1 ≤ T) (hB : 0 < B) (hBT : B ≤ T)
    (σc : ℝ) (hσc₀ : 0 < σc) (hσc₁ : σc ≤ 1) (r : ℕ → Fin K → ℝ) (c : ℕ → Fin d → Fin K → ℝ)
    (hc : ∀ (i : Fin d) (a : Fin K), IsStationarySeq σc T (fun t => c t i a))
    (Ts : ℕ) (p : Fin K → ℝ) (hopt : IsOptFDSolution T B r c Ts p) :
    ∀ i : Fin d, ∀ t ∈ Finset.Icc 1 T,
      expect p (fun a => c t i a) ≤ B / T / ((Ts : ℝ) / T * σc) := by
  intro i t ht
  obtain ⟨hTs, hp, hfeas, -⟩ := hopt
  rw [Finset.mem_Icc] at hTs
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hTspos : (0 : ℝ) < Ts := by exact_mod_cast (show 0 < Ts by omega)
  have hs : ∀ s ∈ Finset.Icc 1 Ts, σc * expect p (fun a => c t i a) ≤ expect p (fun a => c s i a) := by
    intro s hsm
    have hsT : s ∈ Finset.Icc 1 T := by
      rw [Finset.mem_Icc] at hsm ⊢; omega
    unfold expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    have h1 := hc i a t ht s hsT
    have h2 := hp.1 a
    simp only at h1
    nlinarith
  have hsum := Finset.sum_le_sum hs
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsum
  have hfi := hfeas i
  have hkey : (Ts : ℝ) * σc * expect p (fun a => c t i a) ≤ B := by
    have : ((Ts + 1 - 1 : ℕ) : ℝ) = Ts := by simp
    rw [this] at hsum
    nlinarith
  have heq : B / T / ((Ts : ℝ) / T * σc) = B / (Ts * σc) := by
    field_simp
  rw [heq, le_div_iff₀ (by positivity)]
  linarith
