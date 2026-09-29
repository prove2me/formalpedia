-- Prove2me | solution 1 for TarchaBraids.artinTits_hom_halfTwist_injective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:38:08.910328+00:00
-- url     : https://prove2.me/submissions/8daa2722-63c0-4c93-8a42-d8efa98bca19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BraidsLinksMCG_artinBraidGroup_equiv_artinTits_generatorMatched
import Theorems.Thm_TarchaBraids_thm_3_15_half_twist_hom_injective
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinTitsA
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG TarchaBraids

theorem _root_.solution (n : ℕ)
    (g : BraidsLinksMCG.artinTitsA n →* GeomBraidGroup n)
    (hg : ∀ i : Fin (n - 1), g (PresentedGroup.of i) = halfTwistBraid n i) :
    Function.Injective g := by
  obtain ⟨e, he⟩ := BraidsLinksMCG.artinBraidGroup_equiv_artinTits_generatorMatched n
  have hf : ∀ i : Fin (n - 1),
      (g.comp e.toMonoidHom) (sigma i) =
        halfTwistBraid n i := by
    intro i
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he i] using hg i
  have hfi := TarchaBraids.thm_3_15_half_twist_hom_injective n
    (g.comp e.toMonoidHom) hf
  intro a b hab
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  exact congrArg e (hfi (by simpa using hab))

#print axioms solution
