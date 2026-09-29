-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.cutOut_smul_of_cutOut_vcFun
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c4c86473-f163-5cc4-b933-8d54a2c63974

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_cutOut_smul_of_cutOut_vcFun

set_option autoImplicit false

theorem solution
    (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)
    (M' : ℕ) [NeZero M'] (h : ↥M'.primeFactors → Polynomial K)
    (hmonic : ∀ p, (h p).Monic) (hdeg : ∀ p : ↥M'.primeFactors, (h p).natDegree ≤ ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
    (g' : (C • W).toAffine.Point)
    (hg : (addOrderOf (WeierstrassCurve.Affine.Point.vcFun C W g') = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : K) (h₁ : (W).toAffine.Nonsingular x₁ y₁),
          n • (WeierstrassCurve.Affine.Point.vcFun C W g') = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • (WeierstrassCurve.Affine.Point.vcFun C W g')) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (h p).IsRoot x₁)) :
    (addOrderOf g' = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : K) (h₁ : (C • W).toAffine.Nonsingular x₁ y₁),
          n • g' = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g') = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) (h p)).IsRoot x₁) := by
  classical
  obtain ⟨hord, hcut⟩ := hg

  have hvc_add : ∀ P Q : (C • W).toAffine.Point,
      WeierstrassCurve.Affine.Point.vcFun C W (P + Q) =
        WeierstrassCurve.Affine.Point.vcFun C W P + WeierstrassCurve.Affine.Point.vcFun C W Q := by
    intro P Q
    have hinj : Function.Injective (WeierstrassCurve.Affine.Point.vcInvFun C W.toAffine) :=
      (WeierstrassCurve.Affine.Point.vcFun_rightInverse (C := C) (W := W.toAffine)).injective
    apply hinj
    rw [WeierstrassCurve.Affine.Point.vcInvFun_add, WeierstrassCurve.Affine.Point.vcFun_leftInverse,
      WeierstrassCurve.Affine.Point.vcFun_leftInverse, WeierstrassCurve.Affine.Point.vcFun_leftInverse]
  let φ : (C • W).toAffine.Point →+ W.toAffine.Point :=
    { toFun := WeierstrassCurve.Affine.Point.vcFun C W
      map_zero' := WeierstrassCurve.Affine.Point.vcFun_zero
      map_add' := hvc_add }
  have hφ : ∀ P, φ P = WeierstrassCurve.Affine.Point.vcFun C W P := fun _ => rfl
  have hφinj : Function.Injective φ :=
    (WeierstrassCurve.Affine.Point.vcFun_leftInverse (C := C) (W := W.toAffine)).injective
  have hordφ : ∀ P, addOrderOf (φ P) = addOrderOf P := fun P => addOrderOf_injective φ hφinj P
  refine ⟨by rw [← hordφ, hφ, hord], ?_⟩
  intro p n x₁ y₁ h₁ hng hordn
  have h1 : n • WeierstrassCurve.Affine.Point.vcFun C W g' =
      WeierstrassCurve.Affine.Point.some (WeierstrassCurve.Affine.vcX C x₁) (WeierstrassCurve.Affine.vcY C x₁ y₁)
        ((WeierstrassCurve.Affine.nonsingular_variableChange_iff x₁ y₁).mp h₁) := by
    rw [← hφ, ← map_nsmul φ, hng]; rfl
  have h2 : addOrderOf (n • WeierstrassCurve.Affine.Point.vcFun C W g') = (p : ℕ) ^ M'.factorization (p : ℕ) := by
    rw [← hφ, ← map_nsmul φ, hordφ, hordn]
  have hroot := hcut p n _ _ _ h1 h2
  simp only [Polynomial.IsRoot, ModularCurve.kernelVariableChangeDeg, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X] at hroot ⊢
  rw [show (↑C.u : K) ^ 2 * x₁ + C.r = WeierstrassCurve.Affine.vcX C x₁ from rfl, hroot, mul_zero]

end S_WeierstrassCurve_Affine_Point_cutOut_smul_of_cutOut_vcFun
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_cutOut_smul_of_cutOut_vcFun (solution)
