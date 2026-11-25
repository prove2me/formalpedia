-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.RankA.free_range_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:34:30.296616+00:00
-- url     : https://prove2.me/submissions/eee9c2d4-af76-40c7-bdb7-86c68cf8ed16

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RankMapLeRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.RankA
variable {S : Type} [CommRing S]
namespace ReciprocityTheory.PGsh.Up.RankA
theorem _root_.solution [IsLocalRing S] {ι : Type} [Fintype ι] [DecidableEq ι] (e : Matrix ι ι S)
    (he : e * e = e) :
    Module.Free S (LinearMap.range e.mulVecLin) ∧ Module.Finite S (LinearMap.range e.mulVecLin) := by
  let s : (ι → S) →ₗ[S] LinearMap.range e.mulVecLin := e.mulVecLin.rangeRestrict
  have hs : s ∘ₗ (LinearMap.range e.mulVecLin).subtype = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨_, y, rfl⟩ := x
    simp [s, Matrix.mulVec_mulVec, he]
  have : Module.Projective S (LinearMap.range e.mulVecLin) :=
    Module.Projective.of_split (LinearMap.range e.mulVecLin).subtype s hs
  have : Module.Finite S (LinearMap.range e.mulVecLin) :=
    Module.Finite.of_surjective s (LinearMap.surjective_rangeRestrict _)
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩
end ReciprocityTheory.PGsh.Up.RankA
