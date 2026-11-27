-- Prove2me | solution 1 for P2M_AlgebraicGeometry_Scheme_IdealSheafData_comap_subscheme__self_48797f87c60f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:49:31.392984+00:00
-- url     : https://prove2.me/submissions/97dc4448-d3ba-473a-9b1d-b9aef348b990

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}
namespace AlgebraicGeometry.Scheme.IdealSheafData
theorem _root_.solution {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.comap I.subschemeι = ⊥ := by
  refine le_antisymm ?_ bot_le
  have h := comap_map_le (⊥ : I.subscheme.IdealSheafData) I.subschemeι
  rwa [map_bot, ker_subschemeι] at h
end AlgebraicGeometry.Scheme.IdealSheafData
