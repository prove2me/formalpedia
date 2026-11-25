-- Prove2me | solution 1 for PositivityTheory.FamInh.ofInfinite_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:26:12.554772+00:00
-- url     : https://prove2.me/submissions/24aebf7a-d38f-4df9-bf60-0b04e429cc67

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_Development_WeilBound_CoreStatements_PlaceConnectedComponents_ArtinKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology GroundTheory.Global GroundTheory.Global.IdeleGroup
open PositivityTheory PositivityTheory.FamInh
namespace PositivityTheory.FamInh
theorem _root_.solution (E : Type) [Field E] [NumberField E] (y : (InfiniteAdeleRing E)ˣ) :
    (ofInfinite y : IdeleGroup E) =
      Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) y :=
  Units.ext rfl
end PositivityTheory.FamInh
