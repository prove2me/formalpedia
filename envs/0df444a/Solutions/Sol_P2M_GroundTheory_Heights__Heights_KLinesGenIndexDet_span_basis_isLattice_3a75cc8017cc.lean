-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesGenIndexDet_span_basis_isLattice_3a75cc8017cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:00:29.294691+00:00
-- url     : https://prove2.me/submissions/f6ab9bfd-cc6f-4513-bb29-3f690a2726dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexDet

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
open GroundTheory.Heights₂.Heights.KLinesGenIndexDet
namespace GroundTheory.Heights₂.Heights.KLinesGenIndexDet
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℚ V] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℚ V) : Submodule.IsLattice ℚ (Submodule.span ℤ (Set.range b)) where
  fg := Submodule.fg_span (Set.finite_range b)
  span_eq_top := by rw [Submodule.span_span_of_tower, b.span_eq]
end GroundTheory.Heights₂.Heights.KLinesGenIndexDet
