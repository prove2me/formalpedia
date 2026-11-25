-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMap_monomial_mul_e624b3c488ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:39:52.488907+00:00
-- url     : https://prove2.me/submissions/34504a80-0fcb-4e40-b6bc-7b0ad9474639

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finsuppProd_chartVar_6986d97a9298

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) (e : (Σ k, ι k) →₀ ℕ) (c : F) :
    chartMap P u (monomial e c) *
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
          (Ideal.Quotient.mk P (chartMonomial u (Finsupp.weight (blockWeight ι) e))) =
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (monomial e c)) := by
  have hy : ∀ k, algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P (X ⟨k, u k⟩)) ≠ 0 := fun k => by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hu k
  rw [← finsuppProd_chartVar, chartMap, aeval_monomial, monomial_eq]
  simp only [map_mul, map_finsuppProd, map_pow]
  rw [mul_assoc, ← Finsupp.prod_mul]
  congr 1
  refine Finsupp.prod_congr fun v _ => ?_
  rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (hy v.1))]
end GroundTheory.Heights₂.Heights.FieldNumbers
