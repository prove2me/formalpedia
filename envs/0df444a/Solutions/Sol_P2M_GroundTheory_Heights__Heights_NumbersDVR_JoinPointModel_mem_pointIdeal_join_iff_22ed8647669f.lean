-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_mem_pointIdeal_join_iff_22ed8647669f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:25:00.80595+00:00
-- url     : https://prove2.me/submissions/31194df3-c74c-4616-ada3-3d15ab2e65a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_tgtEquiv_mcMap_818d2f828477
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_mcIdeal_eq_pointIdeal_dc408f6410cc


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord joinCoord mcMap)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointModel
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointModel
theorem _root_.solution (y : (Σ k, ι k) → Ω)
    (p : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O) :
    p ∈ pointIdeal O (joinCoord y (ptCoord (Ω := Ω))) ↔
      srcEquiv O p ∈ RingHom.ker
        (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω)) := by
  rw [← BundleExamples.mcIdeal_eq_pointIdeal, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal, RingHom.mem_ker, RingHom.mem_ker,
    Polynomial.coe_mapRingHom, ← tgtEquiv_mcMap, map_eq_zero_iff _ (tgtEquiv K Ω).injective]
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointModel
