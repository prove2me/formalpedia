-- Prove2me | solution 1 for ZipfLaw.zipf_infinite_extension
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:34:05.459953+00:00
-- url     : https://prove2.me/submissions/ea6667a1-468b-4d8c-8882-353d2a61d5ec

import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

private lemma harmonic_range (N : ℕ) (s : ℝ) :
    genHarmonic N s = ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ s := by
  induction N with
  | zero => simp [genHarmonic]
  | succ N ih =>
    change (∑ k ∈ Finset.Icc 1 (N + 1), 1 / (k : ℝ) ^ s) = _
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ]
    change genHarmonic N s + 1 / ((N + 1 : ℕ) : ℝ) ^ s = _
    rw [ih]
    simp

private lemma zipf_summable_iff (s : ℝ) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) ↔ 1 < s := by
  have h := Real.summable_one_div_nat_add_rpow 1 s
  have habs : ∀ k : ℕ, |(k : ℝ) + 1| = (k : ℝ) + 1 := fun k =>
    abs_of_pos (by positivity)
  simpa only [habs] using h

private lemma real_term_cast (k : ℕ) (s : ℝ) :
    ((1 / ((k : ℝ) + 1) ^ s : ℝ) : ℂ) = 1 / (k + 1 : ℂ) ^ (s : ℂ) := by
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity)]
  simp

theorem solution (s : ℝ) (hs : 0 ≤ s) :
    (Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) ↔ 1 < s) ∧
      (1 < s → Filter.Tendsto (fun N : ℕ => ((genHarmonic N s : ℝ) : ℂ)) Filter.atTop
        (nhds (riemannZeta s))) ∧
      (s ≤ 1 → Filter.Tendsto (fun N : ℕ => genHarmonic N s) Filter.atTop Filter.atTop) := by
  refine ⟨zipf_summable_iff s, ?_, ?_⟩
  · intro hs1
    have hreal := (zipf_summable_iff s).mpr hs1
    have hcomplex := (Complex.hasSum_ofReal).mpr hreal.hasSum
    have hcomplexSummable : Summable (fun k : ℕ => 1 / (k + 1 : ℂ) ^ (s : ℂ)) :=
      hcomplex.summable.congr (fun k => real_term_cast k s)
    have hsum : HasSum (fun k : ℕ => 1 / (k + 1 : ℂ) ^ (s : ℂ)) (riemannZeta s) := by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs1)]
      exact hcomplexSummable.hasSum
    have hfn : (fun N : ℕ => ((genHarmonic N s : ℝ) : ℂ)) =
        (fun N : ℕ => ∑ k ∈ Finset.range N, 1 / (k + 1 : ℂ) ^ (s : ℂ)) := by
      funext N
      rw [harmonic_range]
      simp only [Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun k _ => real_term_cast k s)
    rw [hfn]
    exact hsum.tendsto_sum_nat
  · intro hs1
    have hnot : ¬Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) := by
      rw [zipf_summable_iff]
      exact not_lt_of_ge hs1
    have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun k : ℕ => by positivity : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + 1) ^ s)).mp hnot
    simpa only [← harmonic_range] using hdiv

#print axioms solution
