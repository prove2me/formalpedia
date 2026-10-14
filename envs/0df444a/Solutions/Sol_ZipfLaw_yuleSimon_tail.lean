-- Prove2me | solution 1 for ZipfLaw.yuleSimon_tail
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:48:46.111984+00:00
-- url     : https://prove2.me/submissions/633fa5fb-7d86-4a50-b284-e231830b502c

import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw Filter Topology

private lemma zipf_gamma_product (a : ℝ) (ha : 0 < a) (n : ℕ) :
    Real.Gamma (a + n + 1) = Real.Gamma a * ∏ j ∈ Finset.range (n + 1), (a + j) := by
  induction n with
  | zero => simp [Real.Gamma_add_one ha.ne', mul_comm]
  | succ n ih =>
    have hpos : 0 < a + n + 1 := by positivity
    rw [Nat.cast_succ, show a + ((n : ℝ) + 1) + 1 = (a + n + 1) + 1 by ring,
      Real.Gamma_add_one hpos.ne', ih]
    conv_rhs => rw [Finset.prod_range_succ]
    push_cast
    ring

private lemma zipf_yule_ratio (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (hk : 1 ≤ k) :
    yuleSimonPMF ρ k / (ρ ^ 2 * Real.Gamma ρ / (k : ℝ) ^ (ρ + 1)) =
      Real.GammaSeq ρ k / Real.Gamma ρ := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hG := Real.Gamma_pos_of_pos hρ
  have hprod : (∏ j ∈ Finset.range (k + 1), (ρ + (j : ℝ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    positivity
  rw [yuleSimonPMF, Real.Gamma_add_one hρ.ne',
    show (k : ℝ) + ρ + 1 = ρ + k + 1 by ring, zipf_gamma_product ρ hρ k,
    Real.GammaSeq, ← Real.Gamma_nat_eq_factorial k, Real.Gamma_add_one hkpos.ne',
    Real.rpow_add hkpos, Real.rpow_one]
  field_simp [hρ.ne', hG.ne', hprod, (Real.rpow_pos_of_pos hkpos ρ).ne']

theorem solution (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧
      Asymptotics.IsEquivalent Filter.atTop (fun k : ℕ => yuleSimonPMF ρ k)
        (fun k : ℕ => C / (k : ℝ) ^ (ρ + 1)) := by
  have hG := Real.Gamma_pos_of_pos hρ
  refine ⟨ρ ^ 2 * Real.Gamma ρ, by positivity, ?_⟩
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hlimit := (Real.GammaSeq_tendsto_Gamma ρ).div_const (Real.Gamma ρ)
  rw [div_self hG.ne'] at hlimit
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  exact (zipf_yule_ratio ρ hρ k hk).symm

#print axioms solution
