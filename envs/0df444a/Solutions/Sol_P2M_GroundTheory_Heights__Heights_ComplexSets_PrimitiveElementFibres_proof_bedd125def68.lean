-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_proof_bedd125def68
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:13.270159+00:00
-- url     : https://prove2.me/submissions/bd2546be-97f3-4b2a-b8b8-d4b6624cfda5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PrimitiveLinearForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_algebraMap_C_eq_62e9e2c24ee5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_adjoin_eq_top_5091f8a7cfeb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_evalAt_projHom_af6e125320e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_eval_pullback_d784c0eada3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_exists_primitive_data_34d085bb3e1a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres
theorem _root_.solution : PrimitiveElementFibres.Statement := by
  intro n d J A hJ _ hA
  have := hJ
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := (projHom J A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) := hA.injective
  obtain ⟨c, m, D, Q, hmon, hdeg, hdiv, hD, ⟨a, b, hab⟩, hQ⟩ :=
    PrimitiveLinearForm.exists_primitive_data hinj (MvPolynomial.C : ℂ →+* (MvPolynomial (Fin d) ℂ))
      (fun j : Fin n => Ideal.Quotient.mk J (X j)) (adjoin_eq_top J A)
  set ℓ : (MvPolynomial (Fin n) ℂ ⧸ J) := ∑ j, algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (C (c j)) * Ideal.Quotient.mk J (X j) with hℓ
  have hℓmk : ℓ = Ideal.Quotient.mk J (∑ j, C (c j) * X j) := by
    rw [hℓ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    congr 1
    exact algebraMap_C_eq J A (c j)

  have hev : ∀ y (x : Fin n → ℂ) (hx : x ∈ fibre J A y) (p : Polynomial (MvPolynomial (Fin d) ℂ)),
      evalAt J x hx.1 (Polynomial.aeval ℓ p) = (p.map (eval y)).eval (∑ j, c j * x j) := by
    intro y x hx p
    have h1 : (evalAt J x hx.1).comp (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) = eval y :=
      RingHom.ext fun P => evalAt_projHom J A hx P
    have h2 : evalAt J x hx.1 ℓ = ∑ j, c j * x j := by
      rw [hℓmk]
      change eval x (∑ j, C (c j) * X j) = _
      simp
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, h1, h2, Polynomial.eval_map]
  refine ⟨c, m, D, Q, hmon, hdeg, hD, fun y hy => ⟨?_, ?_, ?_⟩⟩
  ·
    have h := congrArg (Polynomial.map (eval y)) hab
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      ← Polynomial.derivative_map] at h
    have hu : Polynomial.C (eval y D)⁻¹ * Polynomial.C (eval y D) = (1 : Polynomial ℂ) := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hy, Polynomial.C_1]
    exact ⟨Polynomial.C (eval y D)⁻¹ * a.map (eval y), Polynomial.C (eval y D)⁻¹ * b.map (eval y),
      by linear_combination Polynomial.C (eval y D)⁻¹ * h + hu⟩
  · intro x hx
    refine ⟨?_, fun j => ?_⟩
    · have h := congrArg (evalAt J x hx.1) ((hdiv m).mpr dvd_rfl)
      rw [hev y x hx, map_zero] at h
      exact h
    · have h := congrArg (evalAt J x hx.1) (hQ j)
      have h3 : evalAt J x hx.1 (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) D) =
          eval y D := evalAt_projHom J A hx D
      have h4 : evalAt J x hx.1 (Ideal.Quotient.mk J (X j)) = x j := by simp [evalAt]
      rw [hev y x hx, map_mul, h3, h4] at h
      exact h
  ·
    intro τ hτ
    let _ : Algebra (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) := (Polynomial.aeval ℓ).toRingHom.toAlgebra
    have : IsScalarTower (MvPolynomial (Fin d) ℂ) (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      IsScalarTower.of_algebraMap_eq fun r => (Polynomial.aeval_C ℓ r).symm
    have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.IsIntegral.of_finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)
    have : Algebra.IsIntegral (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ⟨fun s => (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) s).tower_top⟩
    let evτ : Polynomial (MvPolynomial (Fin d) ℂ) →+* ℂ := (Polynomial.evalRingHom τ).comp (Polynomial.mapRingHom (eval y))
    have hmax : (RingHom.ker evτ).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun z => ⟨Polynomial.C (C z), by simp [evτ]⟩)
    have hker : RingHom.ker (algebraMap (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J)) ≤ RingHom.ker evτ := by
      intro p hp
      obtain ⟨q, rfl⟩ := (hdiv p).mp hp
      rw [RingHom.mem_ker, map_mul]
      have : evτ m = 0 := hτ
      rw [this, zero_mul]
    obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := (MvPolynomial (Fin n) ℂ ⧸ J)) _ hker
    have hP' : (P.comap (Ideal.Quotient.mk J)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hP'
    have hmem : ∀ q, Ideal.Quotient.mk J q ∈ P → eval x q = 0 := by
      intro q hq
      have hq' : q ∈ P.comap (Ideal.Quotient.mk J) := hq
      rw [hx] at hq'
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x q).mp hq'
    have hover : ∀ p : Polynomial (MvPolynomial (Fin d) ℂ), evτ p = 0 → Polynomial.aeval ℓ p ∈ P := by
      intro p hp
      have : p ∈ (RingHom.ker evτ) := hp
      rw [← hPc] at this
      exact this
    have hxZ : x ∈ zeroSet J :=
      fun q hq => hmem q (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq]; exact P.zero_mem)
    refine ⟨x, ⟨hxZ, ?_⟩, ?_⟩
    · funext i
      have h1 := hover (Polynomial.C (X i - C (y i))) (by simp [evτ])
      rw [Polynomial.aeval_C] at h1
      have h2 := hmem (pullback A (X i - C (y i))) h1
      rw [FibreBound.eval_pullback] at h2
      simpa [sub_eq_zero] using h2
    · have h1 := hover (Polynomial.X - Polynomial.C (C τ)) (by simp [evτ])
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hℓmk] at h1
      have h3 : algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (C τ) = Ideal.Quotient.mk J (C τ) := algebraMap_C_eq J A τ
      rw [h3, ← map_sub] at h1
      have h2 := hmem _ h1
      simpa [sub_eq_zero] using h2
end GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres
