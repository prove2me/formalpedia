-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_oneBlockPoints_iff_03b7bbff46dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:31:31.879661+00:00
-- url     : https://prove2.me/submissions/443ec0a2-dd1a-4131-8076-2826aeb9d7a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_FunFieldEquivMemChartRingIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_oneBlockIdeal_eq_comap_projIdeal_d8fa3c49585e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (P : ArithVariety n) (k₀ : ι) (w : Fin (n k₀ + 1) → ℂ) :
    w ∈ oneBlockPoints P k₀ ↔
      (fun _ : Unit ↦ w) ∈ Heights.conePoints (P.projIdeal k₀) ℂ := by
  have heval : ∀ f : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ,
      evalCone (fun _ : Unit ↦ w) f =
        eval₂ (Int.castRingHom ℂ) w (rename (blockCoordEquiv (n := n) k₀).symm f) := by
    intro f
    rw [evalCone, eval₂_rename]
    rfl
  constructor
  · rintro ⟨hw, hf⟩
    refine ⟨fun _ ↦ hw, fun f hfI ↦ ?_⟩
    rw [heval]
    refine hf _ ?_
    rw [oneBlockIdeal_eq_comap_projIdeal, Ideal.mem_comap, rename_rename, Equiv.self_comp_symm,
      rename_id_apply]
    exact hfI
  · rintro ⟨hw, hf⟩
    refine ⟨hw (), fun f hfI ↦ ?_⟩
    rw [oneBlockIdeal_eq_comap_projIdeal, Ideal.mem_comap] at hfI
    have h := hf _ hfI
    rw [heval, rename_rename, Equiv.symm_comp_self, rename_id_apply] at h
    exact h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
