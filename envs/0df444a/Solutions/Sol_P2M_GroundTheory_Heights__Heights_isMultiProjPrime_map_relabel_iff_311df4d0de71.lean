-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isMultiProjPrime_map_relabel_iff_311df4d0de71
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:14.598262+00:00
-- url     : https://prove2.me/submissions/4d1a7ac1-a410-488c-a70c-384176ed1368

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isPrime_map_ringEquiv_iff_9444e6a7af2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isRelevant_map_relabel_iff_831acc433198
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomogIdeal_map_relabel_iff_4f1c2e3f1d3b

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (V : Ideal (MRing ι)) :
    IsMultiProjPrime (V.map (relabelRingEquiv ε h)) ↔ IsMultiProjPrime V := by
  unfold IsMultiProjPrime
  rw [isPrime_map_ringEquiv_iff, isMultiHomogIdeal_map_relabel_iff, isRelevant_map_relabel_iff]
end GroundTheory.Heights₂.Heights
