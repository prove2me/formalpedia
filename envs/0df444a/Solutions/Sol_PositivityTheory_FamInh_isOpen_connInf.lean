-- Prove2me | solution 1 for PositivityTheory.FamInh.isOpen_connInf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:26:04.753599+00:00
-- url     : https://prove2.me/submissions/e9d1a62f-0e6b-4fc6-8e14-e729b36d6655

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
theorem _root_.solution (E : Type) [Field E] [NumberField E] :
    IsOpen ((Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ : Subgroup (InfiniteAdeleRing E)ˣ) :
      Set (InfiniteAdeleRing E)ˣ) := by
  haveI : ∀ w : InfinitePlace E, LocallyConnectedSpace w.Completion := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.locallyConnectedSpace
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.locallyConnectedSpace
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E) :=
    inferInstanceAs (LocallyConnectedSpace (∀ w : InfinitePlace E, w.Completion))
  have he : IsOpenEmbedding (Units.val : (InfiniteAdeleRing E)ˣ → InfiniteAdeleRing E) :=
    Units.isOpenEmbedding_val (R := ∀ w : InfinitePlace E, w.Completion)
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E)ˣ := he.locallyConnectedSpace
  exact isOpen_connectedComponent
end PositivityTheory.FamInh
