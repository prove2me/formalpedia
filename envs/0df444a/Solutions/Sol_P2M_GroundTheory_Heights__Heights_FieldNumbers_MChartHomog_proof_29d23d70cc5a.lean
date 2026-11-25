-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartHomog_proof_29d23d70cc5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:06.549374+00:00
-- url     : https://prove2.me/submissions/3a9d566e-5226-4620-826d-65cadb90028c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_add_e11f6d6b4fb2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_isMultiHomog_f53a5f857a85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMap_monomial_mul_e624b3c488ea
import Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_sup
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_sum


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
namespace MChartHomog
theorem _root_.solution : MChartHomog.Statement.{u} := by
  intro F _ K _ _ ι u p
  classical
  obtain ⟨b, hle⟩ : ∃ b : K → ℕ, ∀ e ∈ p.support, Finsupp.weight (blockWeight ι) e ≤ b :=
    ⟨fun k => p.support.sup fun e => Finsupp.weight (blockWeight ι) e k, fun e he k =>
      Finset.le_sup (f := fun e => Finsupp.weight (blockWeight ι) e k) he⟩
  refine ⟨b, ∑ e ∈ p.support,
    monomial e (coeff e p) * chartMonomial u (b - Finsupp.weight (blockWeight ι) e), ?_, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun e he => ?_
    have := (isWeightedHomogeneous_monomial (blockWeight ι) e (coeff e p) rfl).mul
      (chartMonomial_isMultiHomog (F := F) u (b - Finsupp.weight (blockWeight ι) e))
    rwa [add_tsub_cancel_of_le (hle e he)] at this
  · intro P _ hu
    have hY : ∀ c, algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
        (Ideal.Quotient.mk P (chartMonomial u c)) ≠ 0 := fun c => by
      simp only [chartMonomial, map_prod, map_pow]
      refine Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hu k
    rw [eq_div_iff (hY b)]
    conv_lhs => rw [p.as_sum]
    rw [map_sum, Finset.sum_mul, map_sum, map_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have key : (chartMonomial u b : MRing ι F) = chartMonomial u (Finsupp.weight (blockWeight ι) e) *
        chartMonomial u (b - Finsupp.weight (blockWeight ι) e) := by
      rw [← chartMonomial_add, add_tsub_cancel_of_le (hle e he)]
    rw [key, map_mul, map_mul, map_mul, map_mul, ← mul_assoc, chartMap_monomial_mul P u hu]
end MChartHomog
end GroundTheory.Heights₂.Heights.FieldNumbers
