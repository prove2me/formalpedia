-- Prove2me | solution 1 for WHAdditivity.Renyi.renyi_order_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:19:19.880244+00:00
-- url     : https://prove2.me/submissions/a1a26fda-e40f-4a06-9186-e952e193375d

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

open WHAdditivity.Renyi Matrix
open scoped ComplexOrder

lemma trace_cfc_herm {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp [Function.comp_def]

lemma traceRpow_eq {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (p : ℝ) :
    traceRpow p A = ∑ i, hA.eigenvalues i ^ p := by
  unfold traceRpow; rw [trace_cfc_herm hA]
  rw [Complex.re_sum]; simp

lemma vN_eq {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) :
    vonNeumannEntropy A = ∑ i, Real.negMulLog (hA.eigenvalues i) := by
  unfold vonNeumannEntropy; rw [trace_cfc_herm hA]
  rw [Complex.re_sum]; simp

/-- Real-analytic core: probability vector λ. -/
lemma core_bounds {ι : Type} [Fintype ι] (l : ι → ℝ) (h0 : ∀ i, 0 ≤ l i) (h1 : ∑ i, l i = 1)
    (p : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    -Real.log (∑ i, l i ^ (2:ℝ)) ≤ (1 - p)⁻¹ * Real.log (∑ i, l i ^ p) ∧
    (1 - p)⁻¹ * Real.log (∑ i, l i ^ p) ≤ ∑ i, Real.negMulLog (l i) := by
  set q := p - 1 with hq
  have hq0 : 0 < q := by linarith
  have hq1 : q ≤ 1 := by linarith
  have hpow : ∀ i, l i ^ p = l i * l i ^ q := by
    intro i
    have : p = 1 + q := by linarith
    rw [this, Real.rpow_add' (h0 i) (by linarith), Real.rpow_one]
  have hsq : ∀ i, l i ^ (2:ℝ) = l i * l i := by
    intro i; rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
  -- positivity of sums
  obtain ⟨i0, hi0⟩ : ∃ i, 0 < l i := by
    by_contra h; push Not at h
    have : ∑ i, l i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (h0 i)
    linarith
  have hTp : 0 < ∑ i, l i ^ p :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hi0 p)
      (Finset.single_le_sum (f := fun i => l i ^ p) (fun i _ => Real.rpow_nonneg (h0 i) p)
        (Finset.mem_univ i0))
  have hT2 : 0 < ∑ i, l i ^ (2:ℝ) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hi0 2)
      (Finset.single_le_sum (f := fun i => l i ^ (2:ℝ)) (fun i _ => Real.rpow_nonneg (h0 i) 2)
        (Finset.mem_univ i0))
  -- (A) Jensen with x^q
  have hA : ∑ i, l i ^ p ≤ (∑ i, l i ^ (2:ℝ)) ^ q := by
    have := (Real.concaveOn_rpow hq0.le hq1).le_map_sum (t := Finset.univ) (w := l) (p := l)
      (fun i _ => h0 i) h1 (fun i _ => Set.mem_Ici.mpr (h0 i))
    simp only [smul_eq_mul] at this
    simpa [hpow, hsq] using this
  -- (B) Jensen with log
  have hB : q * ∑ i, l i * Real.log (l i) ≤ Real.log (∑ i, l i ^ p) := by
    set t := Finset.univ.filter (fun i => 0 < l i)
    have hzero : ∀ i, i ∉ t → l i = 0 := by
      intro i hi; simp [t] at hi; exact le_antisymm hi (h0 i)
    have ht1 : ∑ i ∈ t, l i = 1 := by
      rw [← h1]; exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hzero i hi)
    have := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := t) (w := l)
      (p := fun i => l i ^ q) (fun i _ => h0 i) ht1
      (fun i hi => Set.mem_Ioi.mpr (Real.rpow_pos_of_pos (by simpa [t] using hi) q))
    simp only [smul_eq_mul] at this
    have e1 : ∑ i ∈ t, l i * Real.log (l i ^ q) = q * ∑ i, l i * Real.log (l i) := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_subset (Finset.subset_univ t) (fun i _ hi => by simp [hzero i hi])]
      apply Finset.sum_congr rfl; intro i hi
      rw [Real.log_rpow (by simpa [t] using hi)]; ring
    have e2 : ∑ i ∈ t, l i * l i ^ q = ∑ i, l i ^ p := by
      rw [← Finset.sum_subset (Finset.subset_univ t) (fun i _ hi => by simp [hzero i hi, Real.zero_rpow (show p ≠ 0 by linarith)])]
      exact Finset.sum_congr rfl (fun i _ => (hpow i).symm)
    rw [e1, e2] at this; exact this
  have h1p : 1 - p < 0 := by linarith
  constructor
  · -- -log T2 ≤ (1-p)⁻¹ log Tp
    have : Real.log (∑ i, l i ^ p) ≤ q * Real.log (∑ i, l i ^ (2:ℝ)) := by
      rw [← Real.log_rpow hT2]; exact Real.log_le_log hTp hA
    have hrw : (1 - p)⁻¹ * Real.log (∑ i, l i ^ p) = -(Real.log (∑ i, l i ^ p) / q) := by
      rw [hq, div_eq_inv_mul, ← neg_mul, ← inv_neg]; ring_nf
    rw [hrw, neg_le_neg_iff, div_le_iff₀ hq0]; linarith
  · have hS : ∑ i, Real.negMulLog (l i) = -∑ i, l i * Real.log (l i) := by
      simp [Real.negMulLog, Finset.sum_neg_distrib]
    have hrw : (1 - p)⁻¹ * Real.log (∑ i, l i ^ p) = -(Real.log (∑ i, l i ^ p) / q) := by
      rw [hq, div_eq_inv_mul, ← neg_mul, ← inv_neg]; ring_nf
    rw [hS, hrw, neg_le_neg_iff, le_div_iff₀ hq0]; linarith

lemma density_eig {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ}
    (hρ : IsDensity ρ) :
    (∀ i, 0 ≤ hρ.1.isHermitian.eigenvalues i) ∧ ∑ i, hρ.1.isHermitian.eigenvalues i = 1 := by
  refine ⟨fun i => hρ.1.eigenvalues_nonneg i, ?_⟩
  have h := hρ.1.isHermitian.trace_eq_sum_eigenvalues
  have h2 : ρ.trace = 1 := hρ.2
  have := congrArg Complex.re (h2.symm.trans h)
  simp [Complex.re_sum] at this
  linarith

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ)
    (hρ : IsDensity ρ) (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    renyiEntropy 2 ρ ≤ renyiEntropy p ρ ∧ renyiEntropy p ρ ≤ vonNeumannEntropy ρ := by
  have hH := hρ.1.isHermitian
  obtain ⟨h0, h1⟩ := density_eig hρ
  have h2 : renyiEntropy 2 ρ = -Real.log (∑ i, hH.eigenvalues i ^ (2:ℝ)) := by
    unfold renyiEntropy; rw [if_neg (by norm_num), traceRpow_eq hH]; norm_num
  rcases eq_or_lt_of_le hp1 with rfl | hp
  · have := (core_bounds _ h0 h1 2 (by norm_num) le_rfl).2
    unfold renyiEntropy at *
    rw [if_pos rfl]
    refine ⟨?_, le_rfl⟩
    rw [if_neg (by norm_num), traceRpow_eq hH, vN_eq hH]; exact this
  · have hpe : renyiEntropy p ρ = (1 - p)⁻¹ * Real.log (∑ i, hH.eigenvalues i ^ p) := by
      unfold renyiEntropy; rw [if_neg (by linarith), traceRpow_eq hH]
    rw [h2, hpe, vN_eq hH]
    exact core_bounds _ h0 h1 p hp hp2
