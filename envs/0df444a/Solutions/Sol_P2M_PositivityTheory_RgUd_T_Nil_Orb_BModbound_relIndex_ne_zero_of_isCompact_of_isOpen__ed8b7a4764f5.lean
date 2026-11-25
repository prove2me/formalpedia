-- Prove2me | solution 1 for P2M_PositivityTheory_RgUd_T_Nil_Orb_BModbound_relIndex_ne_zero_of_isCompact_of_isOpen__ed8b7a4764f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:47:48.480052+00:00
-- url     : https://prove2.me/submissions/8daed429-0ad4-4a5b-a27b-8e2efe764688

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_HaarMeasureGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module ValuativeRel MeasureTheory
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BModbound
namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound
theorem _root_.solution {X : Type} [TopologicalSpace X] [AddCommGroup X]
    [IsTopologicalAddGroup X] (A H : AddSubgroup X) (hA : IsCompact (A : Set X)) (hH : IsOpen (H : Set X))
    (_hle : H ≤ A) : H.relIndex A ≠ 0 := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hopen : IsOpen ((H.addSubgroupOf A : AddSubgroup A) : Set A) :=
    hH.preimage continuous_subtype_val
  haveI : Finite (A ⧸ H.addSubgroupOf A) :=
    AddSubgroup.quotient_finite_of_isOpen _ hopen
  exact AddSubgroup.index_ne_zero_of_finite
end PositivityTheory.RgUd.T.Nil.Orb.BModbound
