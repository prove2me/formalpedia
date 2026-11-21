-- Prove2me | solution 1 for RiemannMasullo.lattice_monomial_evaluation_le_seminorm
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:19:25.684698+00:00
-- url     : https://prove2.me/submissions/16d49567-c5ce-4ba0-a72b-e63839deddb2

-- New supporting theorem for Masullo Appendix D, Remark D.1.3.6.
import Theorems.Thm_RiemannMasullo_elementaryPartial_zero
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
import Mathlib
open RiemannMasullo
open scoped ENNReal

theorem solution (r : ℕ) (f : ElementarySchwartz 0 0 r PUnit) (d : Fin r → ℕ) (a : Fin r → ℤ) :
    (∏ i, |(a i:ℝ)|^d i)*‖f (0,0,a,PUnit.unit)‖ ≤ elementarySchwartzSeminorm (0,0,0,d) f := by
  classical
  let i : ElementarySchwartzIndex 0 0 r := (0,0,0,d)
  have he : (‖(∏ k, (a k:ℂ)^d k) * f (0,0,a,PUnit.unit)‖₊ : ℝ≥0∞) ≤ elementarySchwartzBound f.val i := by
    unfold elementarySchwartzBound
    apply le_iSup_of_le (0 : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 0))
    apply le_iSup_of_le a
    apply le_iSup_of_le PUnit.unit
    simp only [i,elementaryPartial_zero,Pi.zero_apply,pow_zero,Finset.prod_const_one,one_mul]
    rfl
  have h := ENNReal.toReal_mono (f.property.2 i).ne he
  change ‖(∏ k, (a k:ℂ)^d k) * f (0,0,a,PUnit.unit)‖ ≤ _ at h
  rw [norm_mul,Complex.norm_prod] at h
  change _ ≤ (elementarySchwartzBound f.val i).toReal
  simpa [Complex.norm_pow,←Complex.ofReal_intCast, Real.norm_eq_abs] using h
