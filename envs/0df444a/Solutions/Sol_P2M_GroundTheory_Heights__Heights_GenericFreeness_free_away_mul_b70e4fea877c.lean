-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFreeness_free_away_mul_b70e4fea877c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:08:23.6818+00:00
-- url     : https://prove2.me/submissions/a4124172-e174-419b-8edb-3bd682be2c7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_free_iff_of_isLocalizedModule_251d11db15d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_isLocalizedModule_powers_mul_0b09b1d3491f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.GenericFreeness
open Module
universe u
variable {A : Type u} [CommRing A]
namespace GroundTheory.Heights₂.Heights.GenericFreeness
theorem _root_.solution {f : A} (g : A) {M : Type*} [AddCommGroup M] [Module A M]
    (hf : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) :
    Module.Free (Localization.Away (f * g)) (LocalizedModule (Submonoid.powers (f * g)) M) := by
  let Ra := Localization.Away f
  let N := LocalizedModule (Submonoid.powers f) M
  let T := Localization.Away (algebraMap A Ra g)
  let P := LocalizedModule (Submonoid.powers (algebraMap A Ra g)) N
  have hP : Module.Free T P :=
    Module.free_of_isLocalizedModule (Submonoid.powers (algebraMap A Ra g))
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A Ra g)) N)
  haveI := isLocalizedModule_powers_mul f g (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A Ra g)) N)
  exact (free_iff_of_isLocalizedModule (f * g)
    ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A Ra g)) N).restrictScalars A ∘ₗ
      LocalizedModule.mkLinearMap (Submonoid.powers f) M) T).1 hP
end GroundTheory.Heights₂.Heights.GenericFreeness
