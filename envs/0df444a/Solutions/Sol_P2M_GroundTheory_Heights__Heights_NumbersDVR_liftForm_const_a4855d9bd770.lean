-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_const_a4855d9bd770
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:36.641678+00:00
-- url     : https://prove2.me/submissions/0522b5fe-68c8-4323-aeeb-65159ac433be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocalizedQuotientIsSimpleModuleOfMul

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
open MvPolynomial
noncomputable section
universe u
set_option linter.unusedSectionVars false
variable {K : Type} {ι : K → Type} {J : Type} {O : Type*} [CommRing O] [IsDomain O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (a : O) : liftForm (J := J) (C a : MRing ι O) = C a :=
  (liftForm (J := J) (ι := ι) (R := O)).commutes a
end GroundTheory.Heights₂.Heights.NumbersDVR
