-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_t__map_apply_83cb09ba16fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:54:55.263121+00:00
-- url     : https://prove2.me/submissions/dbed4131-1992-4a13-b2dc-d9fc363444ae

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupTate
import Definitions.Def_GroundTheory_TateCohomology_CupTateNatural

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution {S₁ S₂ : ShortComplex (Rep.{u} k G)} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (F : S₁ ⟶ S₂) (i : ℤ) (x : tateCohomology S₁.X₃ i) :
    (tδ h₂ i (i + 1) rfl).hom (((tateCohomologyFunctor i).map F.τ₃).hom x) =
      ((tateCohomologyFunctor (i + 1)).map F.τ₁).hom ((tδ h₁ i (i + 1) rfl).hom x) :=
  congr(($(TateCohomology.δ_naturality h₁ h₂ F i)).hom x).symm
end GroundTheory.GroupCoh
