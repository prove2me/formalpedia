-- Prove2me | solution 1 for PI.WMI.lower_triangular_invariance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:50:57.697393+00:00
-- url     : https://prove2.me/submissions/e1d40fb8-2ab8-4144-afe4-f21b7c5ee4a9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_LowerInv
import Theorems.Thm_PI_WMI_lowerInv_e_mul_pow
import Theorems.Thm_PI_WMI_lowerInv_conj_e
import Theorems.Thm_PI_WMI_lowerInv_evM_affine
import Theorems.Thm_PI_WMI_lowerInv_torus_mem
import Theorems.Thm_PI_WMI_lowerInv_det_ne
import Theorems.Thm_PI_WMI_lowerInv_comm
import Theorems.Thm_PI_WMI_lowerInv_adj
import Theorems.Thm_PI_WMI_lowerInv_not_cdom
import Theorems.Thm_PI_WMI_lowerInv_coeff_scale
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
namespace PI.WMI
theorem _root_.solution : LowerInv := by
  intro N Λ H _ _ σ S K P hU hKT hP hPσ v0 hv0 a b hab c x
  have : FiniteDimensional ℂ S := hKT.1
  have hex : ∀ y : S, ∃ p : Polynomial ℂ, ∀ c : ℂ,
      p.eval c = ⟪v0, P (1 + Matrix.single b a c) y⟫_ℂ := by
    intro y
    obtain ⟨Q, hQ⟩ := hP.poly y v0
    obtain ⟨p, hp⟩ := lowerInv_evM_affine 1 (Matrix.single b a 1) Q
    refine ⟨p, fun c => ?_⟩
    rw [← hp c, hQ, Matrix.smul_single, smul_eq_mul, mul_one]
  choose pp hpp using hex
  have hadd : ∀ y z : S, pp (y + z) = pp y + pp z := fun y z => Polynomial.funext fun c => by
    rw [Polynomial.eval_add, hpp, hpp, hpp, map_add, inner_add_right]
  have hsmul : ∀ (r : ℂ) (y : S), pp (r • y) = Polynomial.C r * pp y := fun r y =>
    Polynomial.funext fun c => by
      rw [Polynomial.eval_mul, Polynomial.eval_C, hpp, hpp, map_smul, inner_smul_right]
  let ψ : ℕ → S →ₗ[ℂ] ℂ := fun m =>
    { toFun := fun y => (pp y).coeff m
      map_add' := fun y z => by simp only [hadd, Polynomial.coeff_add]
      map_smul' := fun r y => by
        simp only [hsmul, Polynomial.coeff_C_mul, smul_eq_mul, RingHom.id_apply] }
  have hψ_apply : ∀ m (y : S), ψ m y = (pp y).coeff m := fun _ _ => rfl
  have hstab : ∀ θ (y : S), σ (torus θ) (y : H) ∈ S := fun θ y =>
    hKT.2.1 _ (lowerInv_torus_mem θ) _ y.2

  have hv0eig : ∀ (θ : Fin N → ℝ) (w : H),
      ⟪(v0 : H), σ (torus θ) w⟫_ℂ = lowerInv_e (∑ i, Λ i * θ i) * ⟪(v0 : H), w⟫_ℂ := by
    intro θ w
    have hw : σ (torus (-θ)) (v0 : H) =
        Complex.exp (((∑ i, Λ i * (-θ) i : ℝ) : ℂ) * Complex.I) • (v0 : H) :=
      hv0 (-θ) (lowerInv_torus_mem (-θ))
    rw [lowerInv_adj hU θ, hw, inner_smul_left]
    have := lowerInv_conj_e (∑ i, Λ i * (-θ) i)
    unfold lowerInv_e at this ⊢
    rw [this]
    congr 3
    simp [Finset.sum_neg_distrib]
  have hv0P : ∀ θ (y : S), ⟪v0, P (torus θ) y⟫_ℂ =
      (torus θ).det ^ K * lowerInv_e (∑ i, Λ i * θ i) * ⟪v0, y⟫_ℂ := by
    intro θ y
    rw [Submodule.coe_inner, hPσ _ (lowerInv_torus_mem θ), inner_smul_right, hv0eig,
      Submodule.coe_inner, mul_assoc]
  have hrel : ∀ θ (y : S) (c : ℂ), (pp (P (torus θ) y)).eval c =
      ((torus θ).det ^ K * lowerInv_e (∑ i, Λ i * θ i)) *
        (pp y).eval (c * lowerInv_e (θ a - θ b)) := by
    intro θ y c
    rw [hpp, hpp, ← LinearMap.comp_apply, ← hP.mul, lowerInv_comm hab, hP.mul, LinearMap.comp_apply,
      hv0P]
  have hψ : ∀ m, 1 ≤ m → ψ m = 0 := by
    intro m hm
    let y : S := (InnerProductSpace.toDual ℂ S).symm (LinearMap.toContinuousLinearMap (ψ m))
    have hyx : ∀ z : S, ⟪y, z⟫_ℂ = ψ m z := fun z => by
      rw [InnerProductSpace.toDual_symm_apply]; rfl
    have hsc : ∀ θ (z : S), ψ m (P (torus θ) z) =
        (torus θ).det ^ K * lowerInv_e (∑ i, Λ i * θ i) * lowerInv_e (θ a - θ b) ^ m * ψ m z :=
      fun θ z => by
        rw [hψ_apply, hψ_apply, lowerInv_coeff_scale _ _ _ _ (hrel θ z) m]
    have hwt : IsWtOn (Kset (allPos N)) σ (Λ + (m : ℝ) • root a b) (y : H) := by
      intro θ _
      show σ (torus θ) (y : H) = _
      have key : ∀ z : S, ⟪σ (torus θ) (y : H), (z : H)⟫_ℂ =
          lowerInv_e (∑ i, Λ i * (-θ) i) * lowerInv_e ((-θ) a - (-θ) b) ^ m * ⟪(y : H), (z : H)⟫_ℂ := by
        intro z
        have h1 := hsc (-θ) z
        rw [← hyx, ← hyx, Submodule.coe_inner, Submodule.coe_inner, hPσ _ (lowerInv_torus_mem _),
          inner_smul_right, lowerInv_adj hU, neg_neg, mul_assoc ((torus (-θ)).det ^ K),
          mul_assoc ((torus (-θ)).det ^ K)] at h1
        exact mul_left_cancel₀ (pow_ne_zero _ (lowerInv_det_ne (-θ))) h1
      have hE : lowerInv_e (∑ i, Λ i * (-θ) i) * lowerInv_e ((-θ) a - (-θ) b) ^ m =
          (starRingEnd ℂ) (Complex.exp (((∑ i, (Λ + (m : ℝ) • root a b) i * θ i : ℝ) : ℂ) *
            Complex.I)) := by
        rw [lowerInv_e_mul_pow]
        have := lowerInv_conj_e (∑ i, (Λ + (m : ℝ) • root a b) i * θ i)
        unfold lowerInv_e at this ⊢
        rw [this]
        congr 3
        simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, root, Pi.sub_apply,
          add_mul, Finset.sum_add_distrib, mul_sub, sub_mul, Finset.sum_sub_distrib, Pi.single_apply,
          mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true, mul_neg, Finset.sum_neg_distrib]
        ring
      set ev := Complex.exp (((∑ i, (Λ + (m : ℝ) • root a b) i * θ i : ℝ) : ℂ) * Complex.I)
      let w : S := ⟨σ (torus θ) (y : H), hstab θ y⟩ - ev • y
      have hw0 : ∀ z : S, ⟪w, z⟫_ℂ = 0 := by
        intro z
        rw [inner_sub_left, inner_smul_left, Submodule.coe_inner, Submodule.coe_inner]
        show ⟪σ (torus θ) (y : H), (z : H)⟫_ℂ - _ = 0
        rw [key, hE, sub_self]
      have hw : w = 0 := inner_self_eq_zero.mp (hw0 w)
      have := congrArg (fun u : S => (u : H)) hw
      simp only [w, Submodule.coe_sub, Submodule.coe_smul, ZeroMemClass.coe_zero] at this
      exact sub_eq_zero.mp this
    by_contra hne
    have hy0 : (y : H) ≠ 0 := by
      intro h0
      apply hne
      ext z
      rw [← hyx, Submodule.coe_inner, h0, inner_zero_left]
      rfl
    exact lowerInv_not_cdom hab hm (hKT.2.2.2.2 _ (y : H) y.2 hy0 hwt)
  have hconst : pp x = Polynomial.C ((pp x).coeff 0) := by
    ext m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Polynomial.coeff_C, if_neg (by omega)]
      have := LinearMap.congr_fun (hψ m hm) x
      rw [hψ_apply] at this
      simpa using this
  have h0 := hpp x 0
  rw [Matrix.single_zero, add_zero, hP.one, LinearMap.id_apply] at h0
  rw [← hpp, hconst, Polynomial.eval_C]
  rw [hconst, Polynomial.eval_C] at h0
  exact h0
end PI.WMI
