-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LelongRegularise_exists_poly_of_linEval_eq_zero_1a20ed7e007c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:36.93771+00:00
-- url     : https://prove2.me/submissions/f71a1d73-c197-482d-80b0-bcf68f9ce14f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lift_eval_comp_projHom_14fd47dab21a


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.LelongRegularise
namespace GroundTheory.Heights₂.Heights.LelongRegularise
theorem _root_.solution {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} {u : Fin n → ℂ} (hJ : J.IsPrime) (hA : IsFiniteProjection J A)
    (hu : linForm u ∉ J) :
    ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧
      ∀ y x, x ∈ fibre J A y → linEval u x = 0 → MvPolynomial.eval y P = 0 := by
  classical
  have := hJ
  set a := Ideal.Quotient.mk J (linForm u) with ha_def
  have ha : a ≠ 0 := fun h => hu (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hint : (projHom J A).toRingHom.IsIntegralElem a := hA.finite.to_isIntegral _
  have hex : ∃ k, ∃ p : Polynomial (MvPolynomial (Fin d) ℂ), p.Monic ∧ p.natDegree = k ∧
      p.eval₂ (projHom J A).toRingHom a = 0 := by
    obtain ⟨p, hpm, hp⟩ := hint
    exact ⟨_, p, hpm, rfl, hp⟩
  obtain ⟨p, hpm, hpk, hp⟩ := Nat.find_spec hex
  refine ⟨p.coeff 0, fun h0 => ?_, ?_⟩
  · obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.2 h0
    have hqm : q.Monic := Polynomial.monic_X.of_mul_monic_left hpm
    have hq : q.eval₂ (projHom J A).toRingHom a = 0 := by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_X] at hp
      exact (mul_eq_zero.1 hp).resolve_left ha
    have hlt : q.natDegree < Nat.find hex := by
      rw [← hpk, Polynomial.natDegree_X_mul hqm.ne_zero]
      omega
    exact Nat.find_min hex hlt ⟨q, hqm, rfl, hq⟩
  · rintro y x ⟨hx, hxy⟩ hux
    have h := congrArg (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq) hp
    rw [Polynomial.hom_eval₂, IndefiniteRowSideFullHecke.ComplexSets.lift_eval_comp_projHom J A hx, map_zero] at h
    have hax : (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq) a = 0 := by
      rw [ha_def, Ideal.Quotient.lift_mk, ← hux]
      simp [linForm, linEval]
    rw [hax, Polynomial.eval₂_at_zero, hxy] at h
    exact h
end GroundTheory.Heights₂.Heights.LelongRegularise
