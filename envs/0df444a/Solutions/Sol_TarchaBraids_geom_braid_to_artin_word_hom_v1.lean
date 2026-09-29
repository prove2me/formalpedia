-- Prove2me | solution 1 for TarchaBraids.geom_braid_to_artin_word_hom_v1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T07:56:58.591731+00:00
-- url     : https://prove2.me/submissions/35689f3b-157d-4963-9f6b-8e961e6abcf2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_halfTwist_free_lift_surjective_acyclic_v1
import Theorems.Thm_TarchaBraids_geom_braid_word_relation_sound_v1

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ) :
    ∃ g : GeomBraidGroup n →* ArtinBraidGroup n,
      ∀ i : Fin (n - 1), g (halfTwistBraid n i) = sigma i := by
  classical
  let h : FreeGroup (Fin (n - 1)) →* GeomBraidGroup n :=
    FreeGroup.lift (fun i => halfTwistBraid n i)
  let q : FreeGroup (Fin (n - 1)) →* ArtinBraidGroup n :=
    PresentedGroup.mk (braidRels n)
  have hs : Function.Surjective h :=
    halfTwist_free_lift_surjective_acyclic_v1 n
  have hk : h.ker ≤ q.ker := by
    intro w hw
    apply MonoidHom.mem_ker.mpr
    exact geom_braid_word_relation_sound_v1 n w (MonoidHom.mem_ker.mp hw)
  let e : (FreeGroup (Fin (n - 1)) ⧸ h.ker) ≃* GeomBraidGroup n :=
    QuotientGroup.quotientKerEquivOfSurjective h hs
  let Q : (FreeGroup (Fin (n - 1)) ⧸ h.ker) →* ArtinBraidGroup n :=
    QuotientGroup.lift h.ker q hk
  let g : GeomBraidGroup n →* ArtinBraidGroup n :=
    Q.comp e.symm.toMonoidHom
  refine ⟨g, ?_⟩
  intro i
  have heval :
      e (QuotientGroup.mk (FreeGroup.of i)) = halfTwistBraid n i := by
    change (QuotientGroup.kerLift h) (QuotientGroup.mk (FreeGroup.of i)) = _
    simpa [h] using QuotientGroup.kerLift_mk h (FreeGroup.of i)
  change Q (e.symm (halfTwistBraid n i)) = sigma i
  rw [← heval, e.symm_apply_apply]
  rfl
