-- Prove2me | solution 1 for RiemannMasullo.lattice_monomial_sup_le_weighted_sequence_sum
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:09:59.463998+00:00
-- url     : https://prove2.me/submissions/a745b153-74cd-4073-a504-fea9143d5670

-- New supporting theorem for the sequence identification in Appendix D.
import Theorems.Thm_RiemannMasullo_elementaryPartial_zero
import Definitions.Def_RiemannMasullo_ElementarySchwartzBounds
import Definitions.Def_RiemannMasullo_RapidDecaySequenceBound
import Mathlib
open RiemannMasullo
open scoped ENNReal NNReal

theorem solution (r : ℕ) (s : (Fin r → ℤ) → ℂ) (i : ElementarySchwartzIndex 0 0 r) :
    elementarySchwartzBound (fun g : ElementaryLieGroup 0 0 r PUnit => s g.2.2.1) i ≤
      rapidDecaySequenceBound (∑ k, i.2.2.2 k) s := by
  classical
  let d := i.2.2.2
  have hb : i.2.1 = 0 := Subsingleton.elim _ _
  have hc : i.2.2.1 = 0 := Subsingleton.elim _ _
  simp only [elementarySchwartzBound,hb,hc,elementaryPartial_zero,Finset.prod_empty,
    Finset.univ_eq_empty,one_mul]
  apply iSup_le
  intro x
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  let v : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun k => (a k:ℝ))
  have hk (k : Fin r) : ‖(a k : ℂ)‖₊ ≤ 1+‖v‖₊ := by
    have hh := PiLp.nnnorm_apply_le v k
    have hcast : ‖(a k : ℂ)‖₊ = ‖(a k : ℝ)‖₊ := by
      rw [←Complex.ofReal_intCast,Complex.nnnorm_real]
    rw [hcast]
    exact hh.trans (by simp)
  have hp : (∏ k, ‖(a k : ℂ)‖₊ ^ d k) ≤ (1+‖v‖₊)^(∑ k,d k) := by
    rw [← Finset.prod_pow_eq_pow_sum Finset.univ d (1+‖v‖₊)]
    apply Finset.prod_le_prod'
    intro k _
    exact pow_le_pow_left' (hk k) _
  unfold rapidDecaySequenceBound
  apply le_trans _ (ENNReal.le_tsum a)
  change (‖(∏ k, (a k:ℂ)^d k) * s a‖₊ : ℝ≥0∞) ≤ (1+(‖v‖₊:ℝ≥0∞))^(∑ k,d k) * _
  rw [nnnorm_mul,ENNReal.coe_mul,←ENNReal.coe_one,←ENNReal.coe_add,←ENNReal.coe_pow]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply ENNReal.coe_le_coe.mpr
  exact (Finset.nnnorm_prod_le _ _).trans ((Finset.prod_le_prod' (fun k _ => nnnorm_pow_le _ _)).trans hp)
