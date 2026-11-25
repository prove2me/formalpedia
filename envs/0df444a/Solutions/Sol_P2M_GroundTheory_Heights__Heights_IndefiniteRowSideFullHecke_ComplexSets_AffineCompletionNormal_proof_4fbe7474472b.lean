-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AffineCompletionNormal_proof_4fbe7474472b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:31:29.011451+00:00
-- url     : https://prove2.me/submissions/2522be0b-1e2b-4816-90ac-5655b200b6aa

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ArtinHenselCompletionNoetherian
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFD
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAffineCompletionNormal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatNormalFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibresRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAffineCompletionNormal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_adicCompletion_isLocalRing_of_isMaximal_b375892dfe60
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_isIntegrallyClosed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace AffineCompletionNormal
theorem _root_.solution (hF : FlatNormalFibres.Statement) (hR : FormalFibresRegular.Statement) :
    AffineCompletionNormal.Statement := by
  intro σ _ I m hI hIC hm
  have : I.IsPrime := hI
  have : m.IsMaximal := hm
  have hloc := adicCompletion_isLocalRing_of_isMaximal m (Ideal.fg_of_isNoetherianRing m)
  refine hF (MvPolynomial σ ℂ ⧸ I) (AdicCompletion m (MvPolynomial σ ℂ ⧸ I)) inferInstance inferInstance hloc
    inferInstance inferInstance hIC fun P _ => ?_
  have := hR ℂ (MvPolynomial σ ℂ ⧸ I) inferInstance m hm P
  exact ⟨inferInstance, GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isIntegrallyClosed _⟩
end AffineCompletionNormal
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
