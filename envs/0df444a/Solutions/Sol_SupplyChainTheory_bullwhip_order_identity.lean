-- Prove2me | solution 1 for SupplyChainTheory.bullwhip_order_identity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T22:09:41.048735+00:00
-- url     : https://prove2.me/submissions/a5122997-0d0e-4358-9e4e-b1fb6bd8d9d9

import Mathlib
import Definitions.Def_SupplyChainTheory_bullwhip

set_option autoImplicit false

/-- Telescoping over `Icc 1 m`: `∑ f i - ∑ f (i+1) = f 1 - f (m+1)`. -/
lemma sct_tele_08c68670 (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 m, f i - ∑ i ∈ Finset.Icc 1 m, f (i + 1) = f 1 - f (m + 1) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    linear_combination ih

open SupplyChainTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : AR1Demand P) (C z : ℝ) (L m : ℕ) (hm : 0 < m) (t : ℤ) (ω : Ω) :
    X.order C z L m t ω
      = (1 + (L : ℝ) / m) * X.D (t - 1) ω - ((L : ℝ) / m) * X.D (t - m - 1) ω
        + z * (X.sigmaHat C m t ω - X.sigmaHat C m (t - 1) ω) := by
  have key := sct_tele_08c68670 (fun k : ℕ => X.D (t - (k : ℤ)) ω) m
  have hshift : ∑ i ∈ Finset.Icc 1 m, X.D (t - 1 - (i : ℤ)) ω
      = ∑ i ∈ Finset.Icc 1 m, X.D (t - ((i + 1 : ℕ) : ℤ)) ω := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    push_cast
    ring
  have h1 : X.D (t - ((1 : ℕ) : ℤ)) ω = X.D (t - 1) ω := by
    congr 1
  have h2 : X.D (t - ((m + 1 : ℕ) : ℤ)) ω = X.D (t - m - 1) ω := by
    congr 1
    push_cast
    ring
  rw [h1, h2, ← hshift] at key
  unfold AR1Demand.order AR1Demand.baseStock AR1Demand.muHat
  linear_combination ((L : ℝ) / m) * key
