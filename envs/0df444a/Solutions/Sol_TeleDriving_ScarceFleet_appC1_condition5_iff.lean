-- Prove2me | solution 1 for TeleDriving.ScarceFleet.appC1_condition5_iff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:12:51.197615+00:00
-- url     : https://prove2.me/submissions/18887a04-fe8d-4a03-9475-749cd51109ac

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

set_option autoImplicit false
open TeleDriving.ScarceFleet

lemma td_rho_pos (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : Assumption1 mu s)
    (hsize : StandingSize mu s mbar m lam) (k : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    0 < rho mu lam m k := by
  have hs : 0 < s := hA1.1
  have hlam : 0 < lam := lt_trans (by positivity) hsize.2.1
  have hmu : 0 < mu m k := hA1.2.1 m k ⟨by exact_mod_cast hk1, by exact_mod_cast hkm⟩
  have hk : (0 : ℝ) < k := by exact_mod_cast hk1
  unfold rho
  exact div_pos hlam (mul_pos hk hmu)

lemma td_core (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : Assumption1 mu s)
    (hsize : StandingSize mu s mbar m lam) (n : ℕ) (hn1 : 1 ≤ n) (hnm : n ≤ m) :
    ∃ ρ a : ℝ, 0 < ρ ∧ 0 < a ∧ ρ = rho mu lam m n ∧ a = piMN mu lam m (n - 1) (n - 1) ∧
      piMN mu lam m n n = ρ * a / (1 + ρ * a) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hwpos : ∀ i, i ≤ m → 0 < weight mu lam m i := fun i hi =>
    Finset.prod_pos fun k hk =>
      td_rho_pos mu s lam mbar m hA1 hsize k (Finset.mem_Icc.mp hk).1
        (le_trans (Finset.mem_Icc.mp hk).2 hi)
  have hW : 0 < weight mu lam m n' := hwpos n' (by omega)
  have hS : 0 < 1 + ∑ i ∈ Finset.Icc 1 n', weight mu lam m i :=
    add_pos_of_pos_of_nonneg one_pos
      (Finset.sum_nonneg fun i hi => (hwpos i (le_trans (Finset.mem_Icc.mp hi).2 (by omega))).le)
  have hρ : 0 < rho mu lam m ((n' + 1 : ℕ) : ℝ) := td_rho_pos mu s lam mbar m hA1 hsize (n' + 1) (by omega) hnm
  refine ⟨rho mu lam m ((n' + 1 : ℕ) : ℝ), piMN mu lam m n' n', hρ, ?_, rfl, by simp, ?_⟩
  · unfold piMN; exact div_pos hW hS
  · have hw : weight mu lam m (n' + 1) = weight mu lam m n' * rho mu lam m ((n' + 1 : ℕ) : ℝ) := by
      unfold weight
      rw [Finset.prod_Icc_succ_top (by omega)]
    unfold piMN
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, hw]
    have := hS.ne'
    field_simp

theorem solution (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : Assumption1 mu s)
    (hA2 : Assumption2 mu mbar) (hsize : StandingSize mu s mbar m lam) :
    piMN mu lam m m m > piMN mu lam m (m - 1) (m - 1) ↔
      lam * SL mu lam m m > (m : ℝ) * mu m (m : ℝ) := by
  have hm1 : 1 ≤ m := le_trans hA2.1 hsize.1
  obtain ⟨ρ, a, hρ, ha, hρe, hae, hp⟩ := td_core mu s lam mbar m hA1 hsize m hm1 le_rfl
  have hs : 0 < s := hA1.1
  have hlam : 0 < lam := lt_trans (by positivity) hsize.2.1
  have hmu : 0 < mu m m := hA1.2.1 m m ⟨by exact_mod_cast hm1, le_rfl⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmm : (m : ℝ) * mu m (m : ℝ) = lam / ρ := by
    rw [hρe]; unfold rho
    field_simp
  unfold SL
  rw [← hae, hp, hmm]
  have hd : 0 < 1 + ρ * a := by positivity
  have e : lam * (1 - ρ * a / (1 + ρ * a)) = lam / (1 + ρ * a) := by
    field_simp; ring
  rw [e, gt_iff_lt, gt_iff_lt, lt_div_iff₀ hd, div_lt_div_iff₀ hρ hd]
  constructor
  · intro h
    have : 0 < ρ - 1 - ρ * a := by nlinarith
    nlinarith
  · intro h
    have : 0 < ρ - 1 - ρ * a := by
      by_contra hh
      push_neg at hh
      nlinarith
    nlinarith
