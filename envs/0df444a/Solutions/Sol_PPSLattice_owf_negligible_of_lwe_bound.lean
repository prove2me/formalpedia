-- Prove2me | solution 1 for PPSLattice.owf_negligible_of_lwe_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:44:30.058972+00:00
-- url     : https://prove2.me/submissions/9a88326c-96fd-40ab-8a5f-1261b1ad0fd7

import Mathlib
import Definitions.Def_PPSLattice_LWEHard
import Definitions.Def_PPSLattice_OWFInvProb
import Definitions.Def_PPSLattice_PolyTimeOn

set_option autoImplicit false
open QAlgorithms.Complexity
open PPSLattice

theorem solution (q χ : ℕ → ℕ) (hLWE : LWEHard q χ)
    (f : Str → Str)
    (hbound : ∀ I : RestrictedDec.Adversary, I.Valid →
      ∃ m : ℕ → ℕ, PolyTimeOn (fun n : ℕ => encNat n) (fun n => encNat (m n)) ∧
        ∃ D : RestrictedDec.Adversary, D.Valid ∧
          ∃ ν : ℕ → ℝ, NoisyOWMPC.Negligible ν ∧
            ∀ n, owfInvProb f I n ≤
              |lweDistProb q χ m D n true - lweDistProb q χ m D n false| + ν n) :
    ∀ I : RestrictedDec.Adversary, I.Valid →
      NoisyOWMPC.Negligible (owfInvProb f I) := by
  intro I hI
  obtain ⟨m, hm, D, hD, ν, hν, hbound⟩ := hbound I hI
  have hAdv := hLWE m hm D hD
  constructor
  · intro n
    exact ENNReal.toReal_nonneg
  · intro c hc
    obtain ⟨Na, hNa⟩ := hAdv.2 (c + 1) (by linarith)
    obtain ⟨Nν, hNν⟩ := hν.2 (c + 1) (by linarith)
    refine ⟨max 2 (max Na Nν), ?_⟩
    intro n hn
    have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
    have hnNa : Na ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    have hnNν : Nν ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hpow : (n : ℝ) ^ (-(c + 1)) = (n : ℝ) ^ (-c) / n := by
      rw [show -(c + 1) = -c + (-1 : ℝ) by ring, Real.rpow_add hnpos]
      simp [Real.rpow_neg_one, div_eq_mul_inv, mul_comm]
    calc
      owfInvProb f I n ≤
          |lweDistProb q χ m D n true - lweDistProb q χ m D n false| + ν n := hbound n
      _ ≤ (n : ℝ) ^ (-(c + 1)) + (n : ℝ) ^ (-(c + 1)) :=
        add_le_add (hNa n hnNa) (hNν n hnNν)
      _ = 2 * ((n : ℝ) ^ (-c) / n) := by rw [hpow]; ring
      _ ≤ (n : ℝ) ^ (-c) := by
        have hrpow_nonneg : 0 ≤ (n : ℝ) ^ (-c) := Real.rpow_nonneg hnpos.le _
        have hdiv : 0 ≤ (n : ℝ) ^ (-c) / n := div_nonneg hrpow_nonneg hnpos.le
        calc
          2 * ((n : ℝ) ^ (-c) / n) = ((n : ℝ) ^ (-c) / n) * 2 := mul_comm _ _
          _ ≤ ((n : ℝ) ^ (-c) / n) * n :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast hn2) hdiv
          _ = (n : ℝ) ^ (-c) := div_mul_cancel₀ _ hnne
