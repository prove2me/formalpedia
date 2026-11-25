-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_exists_poly_of_linEval_eq_zero_7478f6dc9d62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:25.131997+00:00
-- url     : https://prove2.me/submissions/6379e41d-7aa4-4f94-b206-ec8b872c75d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightDiff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongWeightDiffLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_eval_pullback_d784c0eada3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_exists_monic_aeval_eq_zero_ca6fb5170379


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]
    (A : Matrix (Fin d) (Fin n) ℂ) (hA : IsFiniteProjection J A) (u : Fin n → ℂ) (hu : linForm u ∉ J) :
    ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧
      ∀ x ∈ zeroSet J, linEval u x = 0 → eval (A *ᵥ x) P = 0 := by
  classical
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  have hs0 : Ideal.Quotient.mk J (linForm u) ≠ 0 := fun h => hu (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hex : ∃ m, ∃ g : Polynomial (MvPolynomial (Fin d) ℂ), g.Monic ∧ g.natDegree = m ∧
      Polynomial.aeval (Ideal.Quotient.mk J (linForm u)) g = 0 := by
    obtain ⟨g, hgm, -, hg⟩ := FibreBound.exists_monic_aeval_eq_zero J A hA (Ideal.Quotient.mk J (linForm u))
    exact ⟨_, g, hgm, rfl, hg⟩
  obtain ⟨g, hgm, hgd, hg⟩ := Nat.find_spec hex
  have hc : g.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr h0
    have hqm : q.Monic := Polynomial.monic_X.of_mul_monic_left hgm
    rw [map_mul, Polynomial.aeval_X] at hg
    refine Nat.find_min hex (m := q.natDegree) ?_ ⟨q, hqm, rfl, (mul_eq_zero.mp hg).resolve_left hs0⟩
    rw [← hgd, Polynomial.natDegree_mul Polynomial.X_ne_zero hqm.ne_zero, Polynomial.natDegree_X]
    omega
  refine ⟨g.coeff 0, hc, fun x hx hux => ?_⟩
  have hmem : Polynomial.eval₂ (pullback A).toRingHom (linForm u) g ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]
    rw [Polynomial.aeval_def] at hg
    exact hg
  have h0 := hx _ hmem
  have hcomp : (eval x).comp (pullback A).toRingHom = eval (A *ᵥ x) :=
    RingHom.ext fun P => FibreBound.eval_pullback A x P
  have hl : eval x (linForm u) = linEval u x := by simp [linForm, linEval]
  rwa [Polynomial.hom_eval₂, hcomp, hl, hux, Polynomial.eval₂_at_zero] at h0
end GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff
