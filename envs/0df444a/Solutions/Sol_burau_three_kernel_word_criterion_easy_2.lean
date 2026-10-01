-- Prove2me | solution 2 for burau_three_kernel_word_criterion_easy
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T20:03:24.282913+00:00
-- url     : https://prove2.me/submissions/2c725ec9-beb8-4c1b-baab-3d57fee274e2

import Definitions.Def_BurauFaithful_UnreducedBurau
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

set_option autoImplicit false

theorem solution (w : FreeGroup (Fin 2))
    (hw : w ∈ Subgroup.normalClosure (BraidsLinksMCG.braidRels 3)) :
    BurauFaithful.burauRep 3 (PresentedGroup.mk (BraidsLinksMCG.braidRels 3) w) = 1 := by
  have hw' : PresentedGroup.mk (BraidsLinksMCG.braidRels 3) w = 1 :=
    PresentedGroup.mk_eq_one_iff.mpr hw
  calc
    _ = BurauFaithful.burauRep 3 1 := congrArg (BurauFaithful.burauRep 3) hw'
    _ = 1 := (BurauFaithful.burauRep 3).map_one

