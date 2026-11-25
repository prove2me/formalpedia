-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_isIntegral_of_map_5350c19fe2cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:42.68281+00:00
-- url     : https://prove2.me/submissions/5f11dc0c-fbe7-4f8f-890f-19c8904350c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PWIdealField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg
theorem _root_.solution {F F' : Type*} [Field F] [Field F'] (j : F →+* F') {x : F}
    (h : IsIntegral ℤ (j x)) : IsIntegral ℤ x :=
  (isIntegral_algHom_iff j.toIntAlgHom j.injective).1 h
end GroundTheory.Heights₂.Heights.ChowlaSelberg
