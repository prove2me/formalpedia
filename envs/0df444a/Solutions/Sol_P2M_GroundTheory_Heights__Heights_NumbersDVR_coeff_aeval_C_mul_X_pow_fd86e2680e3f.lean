-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_coeff_aeval_C_mul_X_pow_fd86e2680e3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:51.170522+00:00
-- url     : https://prove2.me/submissions/a68ca90a-8dc2-4a0b-a9a0-58e98c3520c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsReesAlgebraDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_monomial__48ac7adff2ee

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
variable {σ : Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {B : Type*} [CommRing B] [Algebra R B] (a : σ → B) (ω : σ → ℕ)
    (n : ℕ) (p : MvPolynomial σ R) :
    (aeval (fun v => Polynomial.C (a v) * Polynomial.X ^ ω v) p).coeff n =
      aeval a (weightedHomogeneousComponent ω n p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have h : aeval (fun v => Polynomial.C (a v) * Polynomial.X ^ ω v) (monomial d c) =
        Polynomial.C (aeval a (monomial d c)) * Polynomial.X ^ (Finsupp.weight ω d) := by
      rw [aeval_monomial, aeval_monomial, Finsupp.weight_apply, Finsupp.prod, Finsupp.prod,
        Finsupp.sum, Polynomial.algebraMap_apply]
      simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum,
        ← Polynomial.C_pow, ← map_prod, map_mul, smul_eq_mul, mul_comm (ω _)]
      ring
    rw [h, Polynomial.coeff_C_mul_X_pow, weightedHomogeneousComponent_monomial']
    by_cases hd : Finsupp.weight ω d = n
    · rw [if_pos hd.symm, if_pos hd]
    · rw [if_neg (Ne.symm hd), if_neg hd, map_zero]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
end GroundTheory.Heights₂.Heights.NumbersDVR
