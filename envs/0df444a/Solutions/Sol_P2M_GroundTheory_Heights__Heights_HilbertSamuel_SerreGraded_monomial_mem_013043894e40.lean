-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_monomial_mem_013043894e40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:21.363469+00:00
-- url     : https://prove2.me/submissions/d436b198-4ce2-45ed-b329-bd175c7e5652

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_prod_X_pow_2f1a1840c1ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_smul_eq_af68eef4f60e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
open Polynomial
variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
variable [Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
theorem _root_.solution (hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w) {n : ℕ} {x : Ω}
    (hx : x ∈ gradedSpan w d t n) : C x * X ^ n ∈ gradedModule q d t := by
  have hle : gradedSpan w d t n ≤ ((gradedModule q d t).toAddSubgroup).comap
      ((Polynomial.monomial n : Ω →ₗ[Ω] (Polynomial Ω)).toAddMonoidHom) := by
    rw [gradedSpan, AddSubgroup.closure_le]
    rintro _ ⟨l, μ, hμ, rfl⟩
    change (Polynomial.monomial n) (t l * ∏ j, w j ^ μ j) ∈ gradedModule q d t
    have heq : (∏ j, MvPolynomial.X j ^ μ j : MvPolynomial (Fin q) ℤ) • (C (t l) * X ^ d l) =
        Polynomial.monomial n (t l * ∏ j, w j ^ μ j) := by
      rw [smul_eq w hA, act_prod_X_pow, ← C_mul_X_pow_eq_monomial, ← hμ, C_mul, pow_add]
      ring
    rw [← heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have := hle hx
  simpa [C_mul_X_pow_eq_monomial] using this
end GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
