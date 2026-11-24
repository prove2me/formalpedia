-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_PlueckerHadamard_intersectionNumber_baseChange_f2b0b1b7bb25
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:10:31.216257+00:00
-- url     : https://prove2.me/submissions/d2aaa7a3-7c7a-431e-810a-0cb9a8353f7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Pluecker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open Matrix Finset
open scoped ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace PlueckerHadamard
theorem _root_.solution : PlueckerHadamard.Statement := by
  intro p q Z hZ
  set H := 1 + Z * Z.conjTranspose with hHdef
  have hpsd : H.PosSemidef := Matrix.PosSemidef.one.add (posSemidef_self_mul_conjTranspose Z)
  have hH : H.IsHermitian := hpsd.isHermitian
  set ev := hH.eigenvalues
  have hev : ∀ i, 0 ≤ ev i := hpsd.eigenvalues_nonneg
  have hdet : H.det = ((∏ i, ev i : ℝ) : ℂ) := by
    rw [hH.det_eq_prod_eigenvalues]; push_cast; rfl
  have htrH : H.trace = ((p * (1 + q) : ℝ) : ℂ) := by
    have hZZ : (Z * Z.conjTranspose).trace = ((p * q : ℕ) : ℂ) := by
      simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply]
      have : ∀ i j, Z i j * (starRingEnd ℂ) (Z i j) = 1 := by
        intro i j
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hZ i j]
        simp
      simp [this]
    rw [hHdef, trace_add, trace_one, hZZ]
    push_cast
    simp
    ring
  have hsum : ∑ i, ev i = p * (1 + q) := by
    have h1 := hH.trace_eq_sum_eigenvalues
    rw [htrH] at h1
    have : ((∑ i, ev i : ℝ) : ℂ) = ((p * (1 + q) : ℝ) : ℂ) := by
      rw [h1]; push_cast; rfl
    exact_mod_cast this
  rw [hdet, Complex.ofReal_re]
  push_cast
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp
  · have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hamgm := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ)
      (fun _ : Fin p => 1 / (p : ℝ)) ev (fun i _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
      (fun i _ => hev i)
    have hrhs : ∑ i, 1 / (p : ℝ) * ev i = 1 + q := by
      rw [← Finset.mul_sum, hsum]; field_simp
    rw [hrhs] at hamgm
    have hprod : ∏ i, ev i = (∏ i, ev i ^ (1 / (p : ℝ))) ^ p := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hev i), one_div_mul_cancel hp'.ne', Real.rpow_one]
    rw [hprod]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hev i) _) hamgm p
end PlueckerHadamard
end GroundTheory.Heights₂.Heights.RestTerms
