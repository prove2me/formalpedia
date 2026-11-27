-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_proof_ae1a634ebc27
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:09:08.427613+00:00
-- url     : https://prove2.me/submissions/e8ef48d2-f358-482f-ac44-ffa31e3be40b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_PPolarisationCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_coeff_polarPoly_d5a631653db6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_coeff_outerDot_pow_444d2d139d6f

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.TheoremB
namespace PolarisationCoeff
theorem _root_.solution : PolarisationCoeff.Statement := by
  intro σ _ Φ n m hm
  classical
  have hneg : ((-1 : MvPolynomial σ (MvPolynomial σ ℝ)) ^ n) = C ((-1 : MvPolynomial σ ℝ) ^ n) := by
    simp
  rw [PolarisationCoeff.coeff_polarPoly, neg_pow (outerDot σ ℝ), hneg, coeff_C_mul,
    PolarisationCoeff.coeff_outerDot_pow n m hm]
  have hsmul : (-1 : MvPolynomial σ ℝ) ^ n * ((Nat.multinomial univ m : MvPolynomial σ ℝ) * monomial m 1) =
      ((-1 : ℝ) ^ n * (Nat.multinomial univ m : ℝ)) • monomial m 1 := by
    rw [smul_eq_C_mul, C_mul, C_pow, C_neg, C_1, map_natCast (C : ℝ →+* MvPolynomial σ ℝ), mul_assoc]
  rw [hsmul, map_smul, smul_eq_mul]
  have hsum : ∑ v, m v = n := by rw [← hm, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  have hprod : (m.prod fun _ e => (e.factorial : ℝ)) * (Nat.multinomial univ m : ℝ) = (n.factorial : ℝ) := by
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp), ← hsum]
    exact_mod_cast Nat.multinomial_spec univ m
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hsq : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by rw [← mul_pow]; simp
  calc Φ (monomial m 1)
      = ((-1 : ℝ) ^ n * (-1) ^ n) * (((m.prod fun _ e => (e.factorial : ℝ)) *
          (Nat.multinomial univ m : ℝ)) / (n.factorial : ℝ)) * Φ (monomial m 1) := by
        rw [hsq, hprod, div_self hn, one_mul, one_mul]
    _ = _ := by ring
end PolarisationCoeff
end GroundTheory.Heights₂.Heights.TheoremB
