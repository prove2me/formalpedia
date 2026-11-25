-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_det_le_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:20:22.40651+00:00
-- url     : https://prove2.me/submissions/87cd39c9-475b-46ad-af50-50925ddd5c28

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℂ) (hN : N.PosSemidef)
    (c : ℝ) (hc : ∀ k, (N k k).re ≤ c) : ‖N.det‖ ≤ c ^ Fintype.card n := by
  classical
  have hH := hN.isHermitian
  have hdet : N.det = ∏ i, (hH.eigenvalues i : ℂ) := hH.det_eq_prod_eigenvalues
  have hl : ∀ i, 0 ≤ hH.eigenvalues i := hN.eigenvalues_nonneg
  have htr : ∑ i, hH.eigenvalues i = ∑ k, (N k k).re := by
    have h2 := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum, Complex.ofReal_re] at h2
    exact h2.symm
  have hnorm : ‖N.det‖ = ∏ i, hH.eigenvalues i := by
    rw [hdet, norm_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [Complex.norm_real, Real.norm_of_nonneg (hl i)]
  rw [hnorm]
  have hsum : ∑ i, hH.eigenvalues i ≤ Fintype.card n * c := by
    rw [htr]
    calc ∑ k, (N k k).re ≤ ∑ _k : n, c := Finset.sum_le_sum fun k _ => hc k
      _ = Fintype.card n * c := by simp
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp h0
    simp [h0]
  · have hm : (0 : ℝ) < Fintype.card n := by exact_mod_cast hpos
    have hAM := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (1 : ℝ) / Fintype.card n)
      hH.eigenvalues (fun i _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp) (fun i _ => hl i)
    have h2 : ∑ i, (1 : ℝ) / Fintype.card n * hH.eigenvalues i ≤ c := by
      rw [← Finset.mul_sum, div_mul_eq_mul_div, one_mul, div_le_iff₀ hm]
      linarith
    have hG : 0 ≤ ∏ i, hH.eigenvalues i ^ ((1 : ℝ) / Fintype.card n) :=
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hl i) _
    calc ∏ i, hH.eigenvalues i = (∏ i, hH.eigenvalues i ^ ((1 : ℝ) / Fintype.card n)) ^ Fintype.card n := by
          rw [← Finset.prod_pow]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← Real.rpow_natCast, ← Real.rpow_mul (hl i), one_div_mul_cancel hm.ne', Real.rpow_one]
      _ ≤ c ^ Fintype.card n := pow_le_pow_left₀ hG (hAM.trans h2) _
end ReciprocityTheory.MultiplicativeHeights
