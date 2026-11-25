-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_Relabel_multAt_map_1cf6a0a0a11f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:31.616835+00:00
-- url     : https://prove2.me/submissions/101cd292-c542-4c79-bb75-b6d0fe9ac2ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isPrime_map_ringEquiv_iff_9444e6a7af2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_localizedModule_quotient_map_06587b043cc3


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
theorem _root_.solution (J W : Ideal (MRingOver F ι)) :
    multAt (J.map (ringEquiv F e h)) (W.map (ringEquiv F e h)) = multAt J W := by
  unfold multAt
  by_cases hW : W.IsPrime
  · have hW' : (W.map (ringEquiv F e h)).IsPrime := (isPrime_map_ringEquiv_iff _ W).2 hW
    rw [dif_pos hW, dif_pos hW']
    exact congrArg ENat.toNat (length_localizedModule_quotient_map (ringEquiv F e h) J W)
  · have hW' : ¬ (W.map (ringEquiv F e h)).IsPrime :=
      fun h' => hW ((isPrime_map_ringEquiv_iff _ W).1 h')
    rw [dif_neg hW, dif_neg hW']
end GroundTheory.Heights₂.Heights.Targets.Relabel
