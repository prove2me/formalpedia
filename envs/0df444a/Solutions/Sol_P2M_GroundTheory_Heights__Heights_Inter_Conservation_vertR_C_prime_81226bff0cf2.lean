-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Conservation_vertR_C_prime_81226bff0cf2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:32:49.856593+00:00
-- url     : https://prove2.me/submissions/0eb94efb-8058-4b06-8699-28f1464e0b5e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Conservation_not_horizontal_d25330750319
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Conservation_charOf_eq_fb1e6fa2063a

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.Inter.Conservation
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.Conservation
theorem _root_.solution (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) {p : ℕ} (hp : p.Prime) :
    vertR P L (C (p : ℤ)) = Real.log p * ∑ V ∈ (divSupp_finite P (C (p : ℤ))).toFinset,
      (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum n V (fun j => (L j).a) : ℝ) := by
  unfold vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Set.Finite.mem_toFinset] at hV
  rw [if_neg (not_horizontal hp hV), charOf_eq hp hV]
  ring
end GroundTheory.Heights₂.Heights.Inter.Conservation
