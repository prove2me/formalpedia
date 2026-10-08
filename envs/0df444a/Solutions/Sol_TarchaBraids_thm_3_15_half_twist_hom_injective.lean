-- Prove2me | solution 1 for TarchaBraids.thm_3_15_half_twist_hom_injective
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T06:02:28.040217+00:00
-- url     : https://prove2.me/submissions/63a1fa94-90ff-4b7e-815f-7247ce28ff60

import Theorems.Thm_BraidsLinksMCG_artinBraidGroup_equiv_artinTits_generatorMatched
import Theorems.Thm_TarchaBraids_artinTits_hom_halfTwist_injective
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_BraidsLinksMCG_ArtinTitsA

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.all false

open BraidsLinksMCG TarchaBraids

theorem _root_.solution (n : ℕ) (f : ArtinBraidGroup n →* GeomBraidGroup n)
    (hf : ∀ i : Fin (n - 1), f (sigma i) = halfTwistBraid n i) :
    Function.Injective f := by
  obtain ⟨e, he⟩ :=
    BraidsLinksMCG.artinBraidGroup_equiv_artinTits_generatorMatched n
  have hg : ∀ i : Fin (n - 1),
      (f.comp (e.symm : BraidsLinksMCG.artinTitsA n →* ArtinBraidGroup n))
          (PresentedGroup.of i) = halfTwistBraid n i := by
    intro i
    have hsym : (e.symm : BraidsLinksMCG.artinTitsA n →* ArtinBraidGroup n)
        (PresentedGroup.of i) = sigma i := by
      rw [← he i]; exact e.symm_apply_apply _
    simp only [MonoidHom.comp_apply, hsym]
    exact hf i
  have hinj := TarchaBraids.artinTits_hom_halfTwist_injective n
    (f.comp (e.symm : BraidsLinksMCG.artinTitsA n →* ArtinBraidGroup n)) hg
  intro a b hab
  apply e.injective
  apply hinj
  simpa using hab

#print axioms solution
