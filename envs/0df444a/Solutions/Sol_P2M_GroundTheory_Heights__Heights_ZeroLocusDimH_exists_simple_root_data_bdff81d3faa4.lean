-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_exists_simple_root_data_bdff81d3faa4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:31:36.306591+00:00
-- url     : https://prove2.me/submissions/ea3c9141-ee33-4550-94ce-cb9de7a33b6a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHAlg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_ringKrullDim_le_of_isIntegral_inj_3b28e03143b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_aeval_derivative_minpoly_ne_zero_2c82d18c6b29

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH
namespace GroundTheory.Heights₂.Heights.ZeroLocusDimH
theorem _root_.solution {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [hp : p.IsPrime] :
    ∃ s : ℕ, (s : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ∧
    ∃ (π : Fin s → MvPolynomial (Fin n) ℂ) (P : Fin n → Polynomial (MvPolynomial (Fin s) ℂ)),
      (∀ i, (P i).eval₂ (MvPolynomial.aeval π).toRingHom (X i) ∈ p) ∧
      (∀ i, (Polynomial.derivative (P i)).eval₂ (MvPolynomial.aeval π).toRingHom (X i) ∉ p) := by
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ p) := Ideal.Quotient.nontrivial_iff.2 hp.ne_top
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℂ (MvPolynomial (Fin n) ℂ ⧸ p)
  let _ : Algebra (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p) := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p) := ⟨hint⟩
  have hdim : ringKrullDim (MvPolynomial (Fin s) ℂ) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  refine ⟨s, hdim ▸ ringKrullDim_le_of_isIntegral_inj hinj, ?_⟩
  choose π hπ using fun j : Fin s => Ideal.Quotient.mk_surjective (I := p) (g (X j))
  have hcomp : (Ideal.Quotient.mk p).comp (MvPolynomial.aeval π).toRingHom =
      algebraMap (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_C]
      change _ = g (C a)
      rw [← MvPolynomial.algebraMap_eq, g.commutes]
      rfl
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X]
      exact hπ j
  have hkey : ∀ (Q : Polynomial (MvPolynomial (Fin s) ℂ)) (i : Fin n),
      Ideal.Quotient.mk p (Q.eval₂ (MvPolynomial.aeval π).toRingHom (X i)) =
        Polynomial.aeval (Ideal.Quotient.mk p (X i)) Q := by
    intro Q i
    rw [Polynomial.hom_eval₂, hcomp, Polynomial.aeval_def]
  have hx : ∀ i : Fin n, IsIntegral (MvPolynomial (Fin s) ℂ) (Ideal.Quotient.mk p (X i)) :=
    fun i => Algebra.IsIntegral.isIntegral _
  refine ⟨π, fun i => minpoly (MvPolynomial (Fin s) ℂ) (Ideal.Quotient.mk p (X i)), fun i => ?_,
    fun i => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, hkey, minpoly.aeval]
  · rw [← Ideal.Quotient.eq_zero_iff_mem, hkey]
    exact aeval_derivative_minpoly_ne_zero hinj _
end GroundTheory.Heights₂.Heights.ZeroLocusDimH
