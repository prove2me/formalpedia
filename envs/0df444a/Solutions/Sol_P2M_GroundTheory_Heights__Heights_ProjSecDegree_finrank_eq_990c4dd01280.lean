-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjSecDegree_finrank_eq_990c4dd01280
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:15:53.80567+00:00
-- url     : https://prove2.me/submissions/05347b85-7490-4281-9eb6-2f8c70ce688a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjSecDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDegree_projVar_ne_zero_598ff16a16a8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDegree_algebraMap_C_5264b9dac3be
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDegree_chartForm_projPar_2d49b4866f36
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDegree_secForm_projPar_ed49e802b14f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDegree_projHom_C_5b049ccef667
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDegree_projHom_X_807c38aad575

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
open GroundTheory.Heights₂.Heights.ProjSecDegree
variable {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)
local notation "𝕂" => FractionRing (MvPolynomial (Fin (e + 1)) ℂ)
local notation "ℝt" => MvPolynomial (Fin (e + 1)) ℂ
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GroundTheory.Heights₂.Heights.ProjSecDegree
theorem _root_.solution [Algebra ℝt (MvPolynomial (Fin n) ℂ ⧸ J)]
    (hφ : ∀ p, algebraMap ℝt (MvPolynomial (Fin n) ℂ ⧸ J) p = ComplexSets.projHom J A p) :
    Module.finrank 𝕂 (TensorProduct ℝt 𝕂 (MvPolynomial (Fin n) ℂ ⧸ J)) =
      Module.finrank 𝕂
        (Vertical.SecAlg (J.map (MvPolynomial.map (algebraMap ℂ 𝕂))) (projPar A)) := by
  let I := Vertical.secIdeal (J.map (MvPolynomial.map (algebraMap ℂ 𝕂))) (projPar A)
  let σ : MvPolynomial (Fin n) ℂ →+* MvPolynomial (Fin n) 𝕂 := MvPolynomial.map (algebraMap ℂ 𝕂)
  have hmkC : ∀ k : 𝕂, Ideal.Quotient.mk I (C k) = algebraMap 𝕂 (MvPolynomial (Fin n) 𝕂 ⧸ I) k :=
    fun _ => rfl
  have hmem : ∀ x ∈ I, Ideal.Quotient.mk I x = 0 := fun _ h => Ideal.Quotient.eq_zero_iff_mem.2 h

  have hunit : IsUnit (algebraMap 𝕂 (MvPolynomial (Fin n) 𝕂 ⧸ I) (projVar e 0)) :=
    (IsUnit.mk0 _ (projVar_ne_zero 0)).map _
  have ha0 : Ideal.Quotient.mk I (σ (ComplexSets.linPoly A 0)) =
      algebraMap 𝕂 (MvPolynomial (Fin n) 𝕂 ⧸ I) (projVar e 0) := by
    have h := hmem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rw [chartForm_projPar, map_sub, map_mul, map_one, hmkC, sub_eq_zero] at h
    calc _ = algebraMap 𝕂 _ (projVar e 0) * (algebraMap 𝕂 _ (projVar e 0)⁻¹ *
          Ideal.Quotient.mk I (σ (ComplexSets.linPoly A 0))) := by
          rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (projVar_ne_zero _), map_one, one_mul]
      _ = _ := by rw [h, mul_one]
  have ha : ∀ i, Ideal.Quotient.mk I (σ (ComplexSets.linPoly A i)) =
      algebraMap 𝕂 (MvPolynomial (Fin n) 𝕂 ⧸ I) (projVar e i) := by
    refine Fin.cases ha0 fun i => ?_
    have h := hmem _ (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
    rw [secForm_projPar, map_sub, map_mul, map_mul, hmkC, hmkC, ha0, sub_eq_zero] at h
    exact hunit.mul_left_cancel (h.symm.trans (mul_comm _ _))

  let ψ : MvPolynomial (Fin n) ℂ ⧸ J →+* MvPolynomial (Fin n) 𝕂 ⧸ I :=
    Ideal.Quotient.lift J ((Ideal.Quotient.mk I).comp σ) fun p hp =>
      hmem _ (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp)))
  have hψ : ψ.comp (algebraMap ℝt _) = algebraMap ℝt (MvPolynomial (Fin n) 𝕂 ⧸ I) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, hφ, projHom_C, Ideal.Quotient.lift_mk, RingHom.comp_apply,
        MvPolynomial.map_C, hmkC, IsScalarTower.algebraMap_apply ℝt 𝕂, algebraMap_C]
    · rw [RingHom.comp_apply, hφ, projHom_X, Ideal.Quotient.lift_mk, RingHom.comp_apply, ha,
        IsScalarTower.algebraMap_apply ℝt 𝕂]
      rfl
  let g : (MvPolynomial (Fin n) ℂ ⧸ J) →ₐ[ℝt] MvPolynomial (Fin n) 𝕂 ⧸ I :=
    { ψ with commutes' := fun r => RingHom.congr_fun hψ r }
  let F := AlgHom.liftEquiv ℝt 𝕂 (MvPolynomial (Fin n) ℂ ⧸ J) (MvPolynomial (Fin n) 𝕂 ⧸ I) g

  let G₀ : MvPolynomial (Fin n) 𝕂 →ₐ[𝕂] TensorProduct ℝt 𝕂 (MvPolynomial (Fin n) ℂ ⧸ J) :=
    aeval fun j => (1 : 𝕂) ⊗ₜ[ℝt] Ideal.Quotient.mk J (X j)
  have hG : G₀.toRingHom.comp σ =
      ((Algebra.TensorProduct.includeRight (R := ℝt) (A := 𝕂)).toRingHom).comp
        (Ideal.Quotient.mk J) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, σ,
        MvPolynomial.map_C, G₀, aeval_C]
      rw [← projHom_C J A, ← hφ, AlgHom.commutes, IsScalarTower.algebraMap_apply ℝt 𝕂, algebraMap_C]
    · simp [G₀, σ]
  have hGa : ∀ i, G₀ (σ (ComplexSets.linPoly A i)) = G₀ (C (projVar e i)) := by
    intro i
    have h := RingHom.congr_fun hG (ComplexSets.linPoly A i)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h
    rw [h, ← projHom_X J A, ← hφ, AlgHom.commutes, IsScalarTower.algebraMap_apply ℝt 𝕂, aeval_C]
    rfl
  have hker : I ≤ RingHom.ker G₀ := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change (G₀.toRingHom.comp σ) p = 0
      rw [hG, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, secForm_projPar, map_sub, map_mul, map_mul, aeval_C,
        aeval_C]
      change _ * G₀ (σ _) - _ * G₀ (σ _) = 0
      rw [hGa, hGa, aeval_C, aeval_C, ← map_mul, ← map_mul, mul_comm (projVar e i.succ), sub_self]
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, chartForm_projPar, ← C_1, map_sub,
        map_mul, aeval_C, aeval_C]
      change _ * G₀ (σ _) - _ = 0
      rw [hGa, aeval_C, ← map_mul, inv_mul_cancel₀ (projVar_ne_zero _), sub_self]
  let G := Ideal.Quotient.liftₐ I G₀ fun a ha => (RingHom.mem_ker).1 (hker ha)
  have h₁ : F.comp G = AlgHom.id 𝕂 _ := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    change F (G₀ (X j)) = Ideal.Quotient.mk I (X j)
    simp only [G₀, aeval_X, F, AlgHom.liftEquiv_tmul, one_smul]
    change ψ (Ideal.Quotient.mk J (X j)) = _
    simp only [ψ, Ideal.Quotient.lift_mk, RingHom.comp_apply, σ, MvPolynomial.map_X]
  have h₂ : G.comp F = AlgHom.id 𝕂 _ := by
    refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
    apply AlgHom.coe_ringHom_injective
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_))
    · rw [RingHom.comp_apply, RingHom.comp_apply, ← projHom_C J A, ← hφ, AlgHom.coe_toRingHom,
        AlgHom.coe_toRingHom, AlgHom.commutes, AlgHom.commutes]
    · simp only [F, G, G₀, g, ψ, σ, RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.coe_comp,
        AlgHom.coe_restrictScalars', Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
        AlgHom.liftEquiv_tmul, one_smul, AlgHom.coe_id, id_eq, AlgHom.coe_mk, Ideal.Quotient.lift_mk,
        MvPolynomial.map_X]
      change G (Ideal.Quotient.mk I (X j)) = _
      exact aeval_X (R := 𝕂) (fun j => (1 : 𝕂) ⊗ₜ[ℝt] Ideal.Quotient.mk J (X j)) j
  exact (AlgEquiv.ofAlgHom G F h₂ h₁).toLinearEquiv.finrank_eq.symm
end GroundTheory.Heights₂.Heights.ProjSecDegree
