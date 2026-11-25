-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twist_sub_eq_203111ec3d6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:13:33.213379+00:00
-- url     : https://prove2.me/submissions/3e2199bd-0e9c-42a5-9772-a5ac9b35c906

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
theorem _root_.solution {L : Type w} [Field L] [Algebra S L] {z : Fin (N + 1) → L}
    (F Q : SubSystem S z L) (I : Chart z) : (F.twist Q).sub I = Q.sub I * F.sub I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, a, ha, rfl⟩
    exact Submodule.mul_mem_mul hq ha
  · exact Submodule.mul_le.mpr fun q hq a ha => Submodule.subset_span ⟨q, hq, a, ha, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
