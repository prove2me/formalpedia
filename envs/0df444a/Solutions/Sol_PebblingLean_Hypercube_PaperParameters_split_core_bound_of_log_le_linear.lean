-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.split_core_bound_of_log_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:55:37.367647+00:00
-- url     : https://prove2.me/submissions/4031a935-fc17-4adc-8efa-704b131d53a0

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {K : ℝ} {n : ℕ}
    (hK : 0 ≤ K)
    (hn8 : 8 ≤ n)
    (hlogLinear : K ^ 2 * Real.log (n : ℝ) ≤ (n : ℝ) / 64) :
    K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1 ≤
      (n : ℝ) / 4 := by
  have hn_pos_nat : 0 < n := by omega
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have harg_nonneg : 0 ≤ (n : ℝ) * Real.log (n : ℝ) :=
    mul_nonneg hn_nonneg hlog_nonneg
  have hx_nonneg :
      0 ≤ K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
    mul_nonneg hK (Real.sqrt_nonneg _)
  have hsq_left :
      (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ^ 2 =
        K ^ 2 * ((n : ℝ) * Real.log (n : ℝ)) := by
    rw [mul_pow, Real.sq_sqrt harg_nonneg]
  have hsq_bound :
      (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ^ 2 ≤
        ((n : ℝ) / 8) ^ 2 := by
    rw [hsq_left]
    calc
      K ^ 2 * ((n : ℝ) * Real.log (n : ℝ)) =
          (n : ℝ) * (K ^ 2 * Real.log (n : ℝ)) := by ring
      _ ≤ (n : ℝ) * ((n : ℝ) / 64) :=
          mul_le_mul_of_nonneg_left hlogLinear hn_nonneg
      _ = ((n : ℝ) / 8) ^ 2 := by ring
  have hn_div8_nonneg : 0 ≤ (n : ℝ) / 8 := by positivity
  have hx_le :
      K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (n : ℝ) / 8 :=
    (sq_le_sq₀ hx_nonneg hn_div8_nonneg).mp hsq_bound
  have hone : (1 : ℝ) ≤ (n : ℝ) / 8 := by
    have hn8_real : (8 : ℝ) ≤ n := by exact_mod_cast hn8
    linarith
  linarith
end PebblingLean.Hypercube.PaperParameters
