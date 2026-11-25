-- Prove2me | solution 1 for PI.FJMB.aeval_translate_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:09.852405+00:00
-- url     : https://prove2.me/submissions/c1960f39-63d4-48e7-b9aa-e0aa134d9c3f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurChain
import Theorems.Thm_PI_FJMB_deriv_aeval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMB
variable {R : Type*} [CommRing R] {σ : Type*}
namespace PI.FJMB
theorem _root_.solution {K : Type*} [Field K] [CharZero K] [Algebra R K] (f : MvPolynomial σ R)
    (S : Finset σ) (c : σ → MvPolynomial σ R) (hf : ∑ v ∈ S, c v * pderiv v f = 0) (y z : σ → K)
    (hz : ∀ v, v ∉ S → z v = 0)
    (hc : ∀ v ∈ S, aeval (fun w => Polynomial.C (y w) + Polynomial.X * Polynomial.C (z w)) (c v) =
      Polynomial.C (z v)) (t : K) :
    aeval (fun w => y w + t * z w) f = aeval y f := by
  classical
  set φ : σ → Polynomial K := fun w => Polynomial.C (y w) + Polynomial.X * Polynomial.C (z w)
    with hφ
  let D : Derivation R (Polynomial K) (Polynomial K) :=
    (Polynomial.derivative' : Derivation K (Polynomial K) (Polynomial K)).restrictScalars R
  have hD : ∀ q, D q = Polynomial.derivative q := fun q => rfl
  have hDφ : ∀ v, D (φ v) = Polynomial.C (z v) := by
    intro v
    rw [hD, hφ]
    simp
  have hS : ∀ v, v ∉ S → D (φ v) = 0 := by
    intro v hv
    rw [hDφ, hz v hv, map_zero]
  have hder : Polynomial.derivative (aeval φ f) = 0 := by
    rw [← hD, deriv_aeval D φ S hS f]
    calc ∑ v ∈ S, aeval φ (pderiv v f) * D (φ v) = ∑ v ∈ S, aeval φ (c v * pderiv v f) := by
          refine Finset.sum_congr rfl (fun v hv => ?_)
          rw [hDφ, map_mul, ← hc v hv, mul_comm]
      _ = aeval φ (∑ v ∈ S, c v * pderiv v f) := by rw [map_sum]
      _ = 0 := by rw [hf, map_zero]
  have hconst : aeval φ f = Polynomial.C ((aeval φ f).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_derivative_eq_zero hder)
  have heval : ∀ (s : K) (g : MvPolynomial σ R),
      (aeval φ g).eval s = aeval (fun w => y w + s * z w) g := by
    intro s g
    induction g using MvPolynomial.induction_on
    · rename_i a
      simp [aeval_C, Polynomial.algebraMap_apply]
    · rename_i p q hp hq
      simp only [map_add, Polynomial.eval_add, hp, hq]
    · rename_i p n hp
      rw [map_mul, aeval_X, Polynomial.eval_mul, hp, map_mul, aeval_X]
      congr 1
      simp only [hφ, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  have h0 : (aeval φ f).eval 0 = aeval y f := by
    have hy : (fun w => y w + 0 * z w) = y := by
      funext w
      simp
    rw [heval 0 f, hy]
  rw [← heval t f, ← h0, hconst, Polynomial.eval_C, Polynomial.eval_C]
end PI.FJMB
