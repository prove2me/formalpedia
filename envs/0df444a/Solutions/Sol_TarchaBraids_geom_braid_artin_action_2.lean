-- Prove2me | solution 2 for TarchaBraids.geom_braid_artin_action
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:06:47.462947+00:00
-- url     : https://prove2.me/submissions/2889832c-267b-4990-928b-da2116d9f536
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BraidsLinksMCG_puncturedPlaneGroup_free_on_standardGen
import Theorems.Thm_TarchaBraids_geom_braid_puncturedPlane_action
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG TarchaBraids

namespace GeomAct

/-- Transport an automorphism group along an isomorphism. -/
def transport {A B : Type*} [Group A] [Group B] (e : A ≃* B) : MulAut A →* MulAut B where
  toFun phi := (e.symm.trans phi).trans e
  map_one' := by ext b; simp
  map_mul' f g := by ext b; simp

@[simp] lemma transport_apply {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (phi : MulAut A) (b : B) : transport e phi b = e (phi (e.symm b)) := rfl

end GeomAct

theorem _root_.solution (n : ℕ) :
    ∃ rho : GeomBraidGroup n →* MulAut (FreeGroup (Fin n)),
      ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
        rho (halfTwistBraid n i) w = artinEndo n i w := by
  obtain ⟨e, he⟩ := BraidsLinksMCG.puncturedPlaneGroup_free_on_standardGen n
  obtain ⟨rho, hrho⟩ := TarchaBraids.geom_braid_puncturedPlane_action n
  have hsymm : ∀ j : Fin n, e.symm (FreeGroup.of j) = standardGen n j := by
    intro j
    rw [← he j, MulEquiv.symm_apply_apply]
  refine ⟨(GeomAct.transport e).comp rho, fun i w => ?_⟩
  have hgen : ∀ j : Fin n,
      ((GeomAct.transport e).comp rho) (halfTwistBraid n i) (FreeGroup.of j)
        = artinEndo n i (FreeGroup.of j) := by
    intro j
    show e (rho (halfTwistBraid n i) (e.symm (FreeGroup.of j))) = _
    rw [hsymm j, hrho i j, artinEndo, FreeGroup.lift_apply_of]
    by_cases h1 : j = strandIdx i
    · rw [if_pos h1, if_pos h1, map_mul, map_mul, map_inv, he, he]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : j = strandIdxSucc i
      · rw [if_pos h2, if_pos h2, he]
      · rw [if_neg h2, if_neg h2, he]
  have hhom : (((GeomAct.transport e).comp rho) (halfTwistBraid n i)).toMonoidHom
      = artinEndo n i := by
    apply FreeGroup.ext_hom
    exact hgen
  exact DFunLike.congr_fun hhom w

#print axioms solution
