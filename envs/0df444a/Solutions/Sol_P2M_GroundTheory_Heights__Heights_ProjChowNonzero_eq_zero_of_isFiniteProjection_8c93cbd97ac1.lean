-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjChowNonzero_eq_zero_of_isFiniteProjection_8c93cbd97ac1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:15:46.952891+00:00
-- url     : https://prove2.me/submissions/e8a9708b-a0f3-4178-a72a-f7c0777eeb57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_smul_of_isHomogeneous_95fca94e9459
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_smul_eq_zero_f2ed159614e3

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
open GroundTheory.Heights₂.Heights.ProjChowNonzero
namespace GroundTheory.Heights₂.Heights.ProjChowNonzero
theorem _root_.solution {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra ℂ Ω] {n d : ℕ}
    {W : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} (hW : IsHomogIdeal W)
    (hA : ComplexSets.IsFiniteProjection W A) {x : Fin n → Ω} (hx : ∀ q ∈ W, aeval x q = 0)
    (hAx : ∀ i, aeval x (ComplexSets.linPoly A i) = 0) : x = 0 := by
  funext j
  by_contra hj
  obtain ⟨p, hpm, hp⟩ := hA.finite.to_isIntegral (Ideal.Quotient.mk W (X j))
  set q := Polynomial.eval₂ (ComplexSets.pullback A).toRingHom (X j) p with hq_def
  have hq : q ∈ W := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hq_def, Polynomial.hom_eval₂]
    exact hp

  set ψ : MvPolynomial (Fin d) ℂ →+* Ω := (algebraMap ℂ Ω).comp (eval 0) with hψ
  have hcomp : ∀ c : Ω, ((aeval (c • x) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Ω) : MvPolynomial (Fin n) ℂ →+* Ω).comp
      (ComplexSets.pullback A).toRingHom = ψ := by
    intro c
    refine MvPolynomial.ringHom_ext (fun a => by simp [hψ, ComplexSets.pullback]) fun i => ?_
    have h1 := aeval_smul_of_isHomogeneous (Ω := Ω) (m := 1) ?_ c x (φ := ComplexSets.linPoly A i)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        ComplexSets.pullback, aeval_X, hψ, eval_X, Pi.zero_apply, map_zero]
      rw [h1, hAx i, mul_zero]
    · exact IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_C_mul_X _ _)
  have hroot : ∀ c : Ω, (p.map ψ).eval (c * x j) = 0 := by
    intro c
    have h := aeval_smul_eq_zero hW hx c q hq
    rw [hq_def, ← AlgHom.coe_toRingHom, Polynomial.hom_eval₂, hcomp c] at h
    simpa [Polynomial.eval_map] using h
  have hzero : p.map ψ = 0 := Polynomial.funext fun r => by
    have := hroot (r / x j)
    rw [div_mul_cancel₀ r hj] at this
    simpa using this
  exact (hpm.map ψ).ne_zero hzero
end GroundTheory.Heights₂.Heights.ProjChowNonzero
