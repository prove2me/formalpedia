-- Prove2me | solution 1 for TroppMatrixConcentration.ch3_tail_spectral_comparison
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:10:46.924585+00:00
-- url     : https://prove2.me/submissions/d56c7c51-fc4a-402d-b152-bcb0f855a222

import Definitions.Def_TroppMatrixConcentration_spectral
import Mathlib.Order.ConditionallyCompleteLattice.Finset

open scoped Matrix.Norms.L2Operator
set_option autoImplicit false
namespace TroppMatrixConcentration

lemma ch3_tail_traceExp_eq_sum {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (θ : ℝ) :
    traceExp (θ • A) = ∑ i, Real.exp (θ * hA.eigenvalues i) := by
  rw [traceExp, matrixExp, ← CFC.real_exp_eq_normedSpace_exp (hA.smul (isSelfAdjoint_iff.mpr (star_trivial θ)))]
  rw [← cfc_comp_const_mul θ Real.exp A (by fun_prop) hA.isSelfAdjoint, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re]

end TroppMatrixConcentration

open TroppMatrixConcentration

theorem solution {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (θ : ℝ) :
    0 ≤ traceExp (θ • A) ∧
    (0 < θ → Real.exp (θ * lambdaMax A) ≤ traceExp (θ • A)) ∧
    (θ < 0 → Real.exp (θ * lambdaMin A) ≤ traceExp (θ • A)) := by
  rw [ch3_tail_traceExp_eq_sum A hA θ]
  have hn : (Set.range hA.eigenvalues).Nonempty := Set.range_nonempty _
  have hf : (Set.range hA.eigenvalues).Finite := Set.finite_range _
  have hmax : lambdaMax A ∈ Set.range hA.eigenvalues := by
    simpa only [lambdaMax, hA.spectrum_real_eq_range_eigenvalues] using hn.csSup_mem hf
  have hmin : lambdaMin A ∈ Set.range hA.eigenvalues := by
    simpa only [lambdaMin, hA.spectrum_real_eq_range_eigenvalues] using hn.csInf_mem hf
  constructor
  · exact Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
  constructor
  · intro _
    obtain ⟨i, hi⟩ := hmax
    rw [← hi]
    exact Finset.single_le_sum (fun j _ => (Real.exp_pos (θ * hA.eigenvalues j)).le) (Finset.mem_univ i)
  · intro _
    obtain ⟨i, hi⟩ := hmin
    rw [← hi]
    exact Finset.single_le_sum (fun j _ => (Real.exp_pos (θ * hA.eigenvalues j)).le) (Finset.mem_univ i)
