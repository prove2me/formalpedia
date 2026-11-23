-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_of_ne_zero_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:30.680439+00:00
-- url     : https://prove2.me/submissions/62094dc4-2d9c-40d0-87bf-a4af7dd44ce2

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : ∀ (m : ℕ) (f : MvPolynomial (Fin m) ℂ), f ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin m → ℂ)), MvPolynomial.eval x f ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro f hf
    refine Filter.Eventually.of_forall fun x => ?_
    rw [MvPolynomial.eq_C_of_isEmpty f] at hf ⊢
    simpa using hf
  | succ m ih =>
    intro f hf
    set P := MvPolynomial.finSuccEquiv ℂ m f with hPdef
    have hP : P ≠ 0 := by
      intro h
      apply hf
      exact (MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hPdef, h, map_zero])
    obtain ⟨k, hk⟩ : ∃ k, P.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      exact hP (Polynomial.ext fun k => by simpa using h k)
    have h1 := ih _ hk
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0
    have he : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ 0
    have hmeas : MeasurableSet {z : ℂ × (Fin m → ℂ) | MvPolynomial.eval (e.symm z) f ≠ 0} :=
      ((MvPolynomial.continuous_eval f).measurable.comp e.symm.measurable)
        (measurableSet_singleton 0).compl
    have key : ∀ᵐ z ∂(volume : Measure (ℂ × (Fin m → ℂ))), MvPolynomial.eval (e.symm z) f ≠ 0 := by
      rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]
      rw [Measure.ae_ae_comm (p := fun y s => MvPolynomial.eval (e.symm (y, s)) f ≠ 0) hmeas]
      filter_upwards [h1] with s hs
      have hQ : Polynomial.map (MvPolynomial.eval s) P ≠ 0 := by
        intro h
        apply hs
        have := congrArg (fun q => Polynomial.coeff q k) h
        simpa [Polynomial.coeff_map] using this
      have hfin : ({y : ℂ | Polynomial.eval y (Polynomial.map (MvPolynomial.eval s) P) = 0}).Finite :=
        Polynomial.finite_setOfPred_isRoot hQ
      have hnull := hfin.measure_zero (volume : Measure ℂ)
      rw [measure_eq_zero_iff_ae_notMem] at hnull
      filter_upwards [hnull] with y hy
      have hc : (e.symm (y, s) : Fin (m + 1) → ℂ) = Fin.cons y s := by
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
      rw [hc, MvPolynomial.eval_eq_eval_mv_eval']
      exact hy
    have := he.quasiMeasurePreserving.ae key
    filter_upwards [this] with x hx
    simpa using hx
end ReciprocityTheory.MultiplicativeHeights
