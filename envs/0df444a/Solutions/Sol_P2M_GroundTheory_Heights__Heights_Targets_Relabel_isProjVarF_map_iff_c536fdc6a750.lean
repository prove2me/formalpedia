-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_Relabel_isProjVarF_map_iff_c536fdc6a750
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:19:18.851697+00:00
-- url     : https://prove2.me/submissions/e0355f33-aca9-4ce6-ab01-531dfb349d5f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_isRelevant_map_iff_e8200a2a6c10
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_isMultiHomogIdeal_map_iff_e68956ff027d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isPrime_map_ringEquiv_iff_9444e6a7af2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_map_34db07ffdc36


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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets GroundTheory.Heights₂.Heights.Targets.Relabel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
  (e : K ≃ K') (h : ∀ k, ι k ≃ ι' (e k))
namespace GroundTheory.Heights₂.Heights.Targets.Relabel
theorem _root_.solution (V : Ideal (MRingOver F ι)) (d : ℕ) :
    IsProjVarF (V.map (ringEquiv F e h)) d ↔ IsProjVarF V d := by
  unfold IsProjVarF IsMultiProjPrime
  rw [isPrime_map_ringEquiv_iff, isMultiHomogIdeal_map_iff, isRelevant_map_iff,
    ringKrullDim_quotient_map, Fintype.card_congr e]
end GroundTheory.Heights₂.Heights.Targets.Relabel
