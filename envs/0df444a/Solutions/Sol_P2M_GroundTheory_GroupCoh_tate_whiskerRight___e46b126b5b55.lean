-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tate_whiskerRight___e46b126b5b55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:57:48.899125+00:00
-- url     : https://prove2.me/submissions/29ae204c-b25d-48ac-ba6a-7f9c6ded3098

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
namespace GroundTheory.GroupCoh
theorem _root_.solution {H : Type u} [Group H] [Fintype H] {F F' : Rep.{u} k G ⥤ Rep.{u} k H}
    [F.PreservesZeroMorphisms] [F'.PreservesZeroMorphisms] (σ : F ⟶ F')
    {X : ShortComplex (Rep.{u} k G)} (hX : (X.map F).ShortExact) (hX' : (X.map F').ShortExact)
    (n : ℤ) :
    TateCohomology.δ hX n ≫ (tateCohomologyFunctor (n + 1)).map (σ.app X.X₁) =
      (tateCohomologyFunctor n).map (σ.app X.X₃) ≫ TateCohomology.δ hX' n :=
  TateCohomology.δ_naturality hX hX' (X.mapNatTrans σ) n
end GroundTheory.GroupCoh
