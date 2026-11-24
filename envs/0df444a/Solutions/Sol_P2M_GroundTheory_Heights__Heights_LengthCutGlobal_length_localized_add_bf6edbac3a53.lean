-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_localized_add_bf6edbac3a53
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:44.557316+00:00
-- url     : https://prove2.me/submissions/d09ad93e-28fc-426c-8b93-22aa67735cd1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutGlobal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthCutGlobal

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
open scoped Pointwise
universe u v
open GroundTheory.Heights₂.Heights.LengthCutGlobal
variable {C : Type u} [CommRing C] (P : Ideal C) [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.LengthCutGlobal
theorem _root_.solution {N M Q : Type*} [AddCommGroup N] [Module C N] [AddCommGroup M]
    [Module C M] [AddCommGroup Q] [Module C Q] (f : N →ₗ[C] M) (g : M →ₗ[C] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl N) +
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl Q) := by
  let fN := LocalizedModule.mkLinearMap P.primeCompl N
  let fM := LocalizedModule.mkLinearMap P.primeCompl M
  let fQ := LocalizedModule.mkLinearMap P.primeCompl Q
  exact Module.length_eq_add_of_exact
    ((IsLocalizedModule.map P.primeCompl fN fM f).extendScalarsOfIsLocalization P.primeCompl
      (Localization.AtPrime P))
    ((IsLocalizedModule.map P.primeCompl fM fQ g).extendScalarsOfIsLocalization P.primeCompl
      (Localization.AtPrime P))
    (IsLocalizedModule.map_injective P.primeCompl fN fM f hf)
    (IsLocalizedModule.map_surjective P.primeCompl fM fQ g hg)
    (IsLocalizedModule.map_exact P.primeCompl fN fM fQ f g H)
end GroundTheory.Heights₂.Heights.LengthCutGlobal
