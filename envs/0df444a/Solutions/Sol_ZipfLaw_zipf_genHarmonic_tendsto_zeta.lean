-- Prove2me | solution 1 for ZipfLaw.zipf_genHarmonic_tendsto_zeta
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T13:32:22.425363+00:00
-- url     : https://prove2.me/submissions/d57eb0af-84d2-48df-a3e3-42f623006f44

import Theorems.Thm_ZipfLaw_zipf_summable_iff
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

private lemma real_term_cast (k : ℕ) (s : ℝ) :
    ((1 / ((k : ℝ) + 1) ^ s : ℝ) : ℂ) = 1 / (k + 1 : ℂ) ^ (s : ℂ) := by
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity)]
  simp

theorem solution (s : ℝ) (hs : 1 < s) :
    Filter.Tendsto (fun N : ℕ => ((genHarmonic N s : ℝ) : ℂ)) Filter.atTop
      (nhds (riemannZeta s)) := by
  have hreal := (zipf_summable_iff s (by linarith)).mpr hs
  have hcomplex := (Complex.hasSum_ofReal).mpr hreal.hasSum
  have hcomplexSummable : Summable (fun k : ℕ => 1 / (k + 1 : ℂ) ^ (s : ℂ)) :=
    hcomplex.summable.congr (fun k => real_term_cast k s)
  have hsum : HasSum (fun k : ℕ => 1 / (k + 1 : ℂ) ^ (s : ℂ)) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
    exact hcomplexSummable.hasSum
  have hfn : (fun N : ℕ => ((genHarmonic N s : ℝ) : ℂ)) =
      (fun N : ℕ => ∑ k ∈ Finset.range N, 1 / (k + 1 : ℂ) ^ (s : ℂ)) := by
    funext N
    rw [harmonic_range]
    simp only [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun k _ => real_term_cast k s)
  rw [hfn]
  exact hsum.tendsto_sum_nat

#print axioms solution
