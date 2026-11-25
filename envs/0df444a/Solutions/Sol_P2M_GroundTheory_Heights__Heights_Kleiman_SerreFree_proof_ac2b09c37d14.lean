-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SerreFree_proof_ac2b09c37d14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:23:08.890811+00:00
-- url     : https://prove2.me/submissions/0e34de19-0535-45c1-98bc-36a1142af9f2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreFree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_sum_freeIncl_freeCoord_02308404be61
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_freeInclusion_toH0_ad3069c41239
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_freeCoordinate_toH0_00580c569653

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SerreFree
theorem _root_.solution (hP : SerrePoly.Statement.{u}) : SerreFree.Statement.{u, v} := by
  intro S _ _ N M _ _ _ _ 𝓜 r b d hb
  obtain ⟨hfin, hpos⟩ := hP S N
  refine ⟨fun i c => ?_, fun c hc => ⟨fun i hi => ?_, ?_, ?_⟩⟩
  · have : ∀ j, Module.Finite S (cohom (polyGraded S N) i (c - d j)) := fun j => hfin i _
    let Φ : ((j : Fin r) → cohom (polyGraded S N) i (c - d j)) →ₗ[S] cohom 𝓜 i c :=
      ∑ j, (freeIncl 𝓜 b d hb i c j).comp (LinearMap.proj j)
    refine Module.Finite.of_surjective Φ fun x => ⟨fun j => freeCoord 𝓜 b d hb i c j x, ?_⟩
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    exact sum_freeIncl_freeCoord 𝓜 b d hb i c x
  · refine ⟨fun x y => ?_⟩
    rw [← sum_freeIncl_freeCoord 𝓜 b d hb i c x, ← sum_freeIncl_freeCoord 𝓜 b d hb i c y]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : Subsingleton (cohom (polyGraded S N) i (c - d j)) :=
      (hpos (c - d j) (by linarith [hc j])).1 i hi
    rw [Subsingleton.elim (freeCoord 𝓜 b d hb i c j x) (freeCoord 𝓜 b d hb i c j y)]
  · rw [injective_iff_map_eq_zero]
    intro m hm
    apply Subtype.ext
    rw [Submodule.coe_zero, ← b.sum_repr m]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h0 := freeCoordinate_toH0 𝓜 b d hb c j m
    rw [hm, map_zero] at h0
    have hinj := (hpos (c - d j) (by linarith [hc j])).2.1
    have : (⟨b.coord j m, coord_mem_piece 𝓜 b d hb m.2 j⟩ : (polyGraded S N).piece (c - d j)) = 0 :=
      hinj (h0.symm.trans (map_zero _).symm)
    rw [← Module.Basis.coord_apply, show b.coord j m = 0 from congrArg Subtype.val this, zero_smul]
  · intro y
    have hsurj := fun j => (hpos (c - d j) (by linarith [hc j])).2.2
    choose p hp using fun j => hsurj j (freeCoord 𝓜 b d hb 0 c j y)
    refine ⟨∑ j, ⟨(p j : Poly S N) • b j, smul_basis_mem 𝓜 b d hb c j (p j)⟩, ?_⟩
    rw [map_sum, ← sum_freeIncl_freeCoord 𝓜 b d hb 0 c y]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hp j, freeInclusion_toH0]
end SerreFree
end GroundTheory.Heights₂.Heights.Kleiman
