-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_psumExpansion_diag_6ef82a32d6d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:25:21.181051+00:00
-- url     : https://prove2.me/submissions/71f0d9f8-719d-45f4-a1ef-e70a0d1f3aa5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PScalarQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_sum_8922677a5a27
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classNum_monomial_124c4592841a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_classList_diag_22aec79530dc

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
theorem _root_.solution {N : ℕ} (x : Fin N → K → ℤ) (k : ℕ) (i : Fin N)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum (Sum.elim x x) (psumExpansion N k i) Q W =
      k * vNumL W (classList x (Finsupp.single i (k - 1)) ++ Q) := by
  unfold psumExpansion
  rw [classNum_sum]
  have key : ∀ j ∈ Finset.range k,
      classNum (Sum.elim x x) (X (Sum.inl i) ^ j * X (Sum.inr i) ^ (k - 1 - j)) Q W =
        vNumL W (classList x (Finsupp.single i (k - 1)) ++ Q) := by
    intro j hj
    have e : j + (k - 1 - j) = k - 1 := by
      have := Finset.mem_range.mp hj
      omega
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul, classNum_monomial, one_mul,
      classList_diag, e]
  rw [Finset.sum_congr rfl key, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
end GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
