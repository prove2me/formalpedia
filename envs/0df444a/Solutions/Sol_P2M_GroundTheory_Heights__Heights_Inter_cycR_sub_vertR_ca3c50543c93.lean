-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_cycR_sub_vertR_ca3c50543c93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:59:06.689+00:00
-- url     : https://prove2.me/submissions/2119bf3c-a722-453d-8ea2-e519354acd92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDerived
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PConsequences

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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) [DecidablePred (IsHorizontal (ι := ι))] :
    cycR I P L s - vertR P L s = ∑ W ∈ (divSupp_finite P s).toFinset.filter IsHorizontal,
      (multAt (P ⊔ Ideal.span {s}) W : ℝ) * I W n L := by
  unfold cycR vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  split_ifs <;> ring
end GroundTheory.Heights₂.Heights.Inter
