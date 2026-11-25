-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_mem_chartIdeal_iff_bfb81604f357
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:28.175221+00:00
-- url     : https://prove2.me/submissions/6679b19f-f206-4bed-87d3-228ae026bd55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartLocDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_chartMonomial_not_mem_42e86f0424ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_algebraMap_mk_ne_zero_5503709ac0c7

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
open GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim
theorem _root_.solution (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) {p h : MRing ι F} {b : K → ℕ}
    (hp : chartMap Q u p = algebraMap (MRing ι F ⧸ Q) (FractionRing (MRing ι F ⧸ Q))
      (Ideal.Quotient.mk Q h) / algebraMap (MRing ι F ⧸ Q) _ (Ideal.Quotient.mk Q (chartMonomial u b))) :
    p ∈ chartIdeal Q u ↔ h ∈ Q := by
  rw [chartIdeal, RingHom.mem_ker, hp, div_eq_zero_iff,
    or_iff_left (algebraMap_mk_ne_zero Q (chartMonomial_not_mem Q u hu b)),
    IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
end GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim
