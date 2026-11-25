-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_intNum_comp_perm_d3826893cbaa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:26.707168+00:00
-- url     : https://prove2.me/submissions/d2587732-84cb-4978-b79f-730faba8816a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsSymmRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_IntNumCompPerm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_comp_perm_7eda8f43bc8a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR
universe u v w
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)) :
    intNum F P (bs ∘ σ) = intNum F P bs := by
  unfold intNum
  rw [FieldNumbers.mixedDiff_comp_perm]
end GroundTheory.Heights₂.Heights.Targets
