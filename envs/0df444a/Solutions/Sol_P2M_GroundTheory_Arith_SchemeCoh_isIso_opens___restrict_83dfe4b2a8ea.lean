-- Prove2me | solution 1 for P2M_GroundTheory_Arith_SchemeCoh_isIso_opens___restrict_83dfe4b2a8ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:10.512829+00:00
-- url     : https://prove2.me/submissions/42984952-f63a-4908-b1fd-60de1adbe70d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_SchemeImage
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_IrreducibleImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
universe u
noncomputable section
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {Z : Scheme.{u}} (O : Z.Opens) : IsIso (O.ι ∣_ O) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply le_antisymm le_top
  intro x _
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change O.ι x ∈ O
    exact x.2
  · apply Subtype.ext
    exact morphismRestrict_base_coe O.ι O ⟨x, _⟩
end GroundTheory.Arith.SchemeCoh
