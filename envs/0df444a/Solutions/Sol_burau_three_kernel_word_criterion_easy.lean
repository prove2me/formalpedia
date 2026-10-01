-- Prove2me | solution 1 for burau_three_kernel_word_criterion_easy
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T19:56:39.632396+00:00
-- url     : https://prove2.me/submissions/feb5cba2-401b-4547-896f-788d639b8e6f

import Definitions.Def_BurauFaithful_UnreducedBurau
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

set_option autoImplicit false

theorem solution (w : FreeGroup (Fin 2))
    (hw : w ∈ Subgroup.normalClosure (BraidsLinksMCG.braidRels 3)) :
    BurauFaithful.burauRep 3 (PresentedGroup.mk (BraidsLinksMCG.braidRels 3) w) = 1 := by
  have hker : w ∈ MonoidHom.ker (FreeGroup.lift (BurauFaithful.burauGen (n := 3))) := by
    rw [MonoidHom.mem_ker]
    exact Subgroup.normalClosure_le_normal
      (fun r hr => MonoidHom.mem_ker.mpr (BurauFaithful.burauGen_relations 3 r hr)) hw
  rw [MonoidHom.mem_ker] at hker
  have hcomp : BurauFaithful.burauRep 3 (PresentedGroup.mk (BraidsLinksMCG.braidRels 3) w)
      = FreeGroup.lift (BurauFaithful.burauGen (n := 3)) w := rfl
  rw [hcomp, hker]
