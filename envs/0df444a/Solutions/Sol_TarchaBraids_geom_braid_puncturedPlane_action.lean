-- Prove2me | solution 1 for TarchaBraids.geom_braid_puncturedPlane_action
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T22:29:44.608356+00:00
-- url     : https://prove2.me/submissions/4fd99c4c-e3e2-4912-bff6-658f31d8b9cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_geom_braid_artin_action_core_v1
import Theorems.Thm_BraidsLinksMCG_puncturedPlaneGroup_free_on_standardGen

open BraidsLinksMCG
open TarchaBraids

theorem solution (n : ℕ) :
    ∃ rho : GeomBraidGroup n →* MulAut (PuncturedPlaneGroup n),
      ∀ i : Fin (n - 1), ∀ j : Fin n,
        rho (halfTwistBraid n i) (standardGen n j) =
          (if j = strandIdx i then
              standardGen n (strandIdx i) * standardGen n (strandIdxSucc i) *
                (standardGen n (strandIdx i))⁻¹
            else if j = strandIdxSucc i then standardGen n (strandIdx i)
            else standardGen n j) := by
  obtain ⟨rho₀, hρ₀⟩ := geom_braid_artin_action_core_v1 n
  obtain ⟨e, he⟩ := puncturedPlaneGroup_free_on_standardGen n
  let rho : GeomBraidGroup n →* MulAut (PuncturedPlaneGroup n) :=
    (MulAut.congr e.symm).toMonoidHom.comp rho₀
  refine ⟨rho, ?_⟩
  intro i j
  apply e.injective
  have hword :
      rho₀ (halfTwistBraid n i) (FreeGroup.of j) =
        artinEndo n i (FreeGroup.of j) := by
    exact hρ₀ i (FreeGroup.of j)
  have htransport :
      rho (halfTwistBraid n i) (standardGen n j) =
        e.symm (rho₀ (halfTwistBraid n i) (e (standardGen n j))) := by
    rfl
  rw [htransport, e.apply_symm_apply, he j, hword]
  simp only [artinEndo, FreeGroup.lift_apply_of]
  by_cases hji : j = strandIdx i
  · subst j
    simp only [if_pos, map_mul, map_inv, he]
  · by_cases hjSucc : j = strandIdxSucc i
    · subst j
      simpa [hji, he]
    · simpa [hji, hjSucc, he]
