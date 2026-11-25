-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_coeff_outerDot_pow_444d2d139d6f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:29:55.868656+00:00
-- url     : https://prove2.me/submissions/ac02d1d4-0984-45ee-b76d-e5bf300a2c8e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_PPolarisationCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_prod_X_pow_eq_monomial_one_4f6397c18364

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
theorem _root_.solution {σ R : Type*} [CommRing R] [Fintype σ] (n : ℕ) (m : σ →₀ ℕ)
    (hm : (m.sum fun _ e => e) = n) :
    coeff m ((outerDot σ R) ^ n) = (Nat.multinomial univ m : MvPolynomial σ R) * monomial m 1 := by
  classical
  unfold outerDot
  rw [Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  have hterm : ∀ k : σ → ℕ,
      (Nat.multinomial univ k : MvPolynomial σ (MvPolynomial σ R)) *
          ∏ v, (X v * C (X v) : MvPolynomial σ (MvPolynomial σ R)) ^ k v =
        monomial (Finsupp.equivFunOnFinite.symm k)
          ((Nat.multinomial univ k : MvPolynomial σ R) *
            monomial (Finsupp.equivFunOnFinite.symm k) 1) := by
    intro k
    simp_rw [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    have h1 := PolarisationCoeff.prod_X_pow_eq_monomial_one (S := MvPolynomial σ R) (Finsupp.equivFunOnFinite.symm k)
    have h2 := PolarisationCoeff.prod_X_pow_eq_monomial_one (S := R) (Finsupp.equivFunOnFinite.symm k)
    simp only [Finsupp.coe_equivFunOnFinite_symm] at h1 h2
    rw [h1, h2, ← map_natCast (C : MvPolynomial σ R →+* _),
      mul_comm (monomial _ (1 : MvPolynomial σ R)) (C _), C_mul_monomial, mul_one, C_mul_monomial]
  simp_rw [hterm, coeff_monomial]
  have hiff : ∀ k : σ → ℕ, Finsupp.equivFunOnFinite.symm k = m ↔ (⇑m : σ → ℕ) = k := by
    intro k
    constructor
    · rintro rfl; rfl
    · rintro rfl; exact Finsupp.equivFunOnFinite.symm_apply_apply m
  simp_rw [hiff]
  rw [Finset.sum_ite_eq]
  have hmem : (⇑m : σ → ℕ) ∈ piAntidiag univ n := by
    rw [mem_piAntidiag]
    refine ⟨?_, fun i _ => mem_univ i⟩
    rw [← hm, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  rw [if_pos hmem, Finsupp.equivFunOnFinite_symm_coe]
end PolarisationCoeff
end GroundTheory.Heights₂.Heights.TheoremB
