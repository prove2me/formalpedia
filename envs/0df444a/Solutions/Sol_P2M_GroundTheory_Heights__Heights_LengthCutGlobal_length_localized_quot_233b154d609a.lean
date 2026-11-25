-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_localized_quot_233b154d609a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:51.850829+00:00
-- url     : https://prove2.me/submissions/320a5f31-2fed-45f4-a031-235c4e6ef03e

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
theorem _root_.solution :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (C ⧸ P)) = 1 := by
  let S := Localization.AtPrime P
  have hJ : (P : Submodule C C).localized' S P.primeCompl (Algebra.linearMap C S) =
      IsLocalRing.maximalIdeal S := by
    rw [Submodule.localized'_eq_span, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map]
    rfl
  let e := (IsLocalizedModule.linearEquiv P.primeCompl
    ((P : Submodule C C).toLocalizedQuotient' S P.primeCompl (Algebra.linearMap C S))
    (LocalizedModule.mkLinearMap P.primeCompl (C ⧸ P))).extendScalarsOfIsLocalization P.primeCompl S
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]
  exact Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.mpr
    (Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal S)))
end GroundTheory.Heights₂.Heights.LengthCutGlobal
