-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_conePoints_projIdeal_iff_3dd345e4b6b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:31:43.917576+00:00
-- url     : https://prove2.me/submissions/daf3e6f3-077d-4f81-881d-19a4c91d5b95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MemConePointsProjIdealIff

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
theorem _root_.solution (P : ArithVariety n) (k₀ : ι)
    (w : Cone (fun _ : Unit ↦ n k₀) ℂ) :
    w ∈ GroundTheory.Heights₂.Heights.conePoints (P.projIdeal k₀) ℂ ↔ w () ∈ oneBlockPoints P k₀ := by
  have hw0 : BlockNonzero w ↔ w () ≠ 0 := ⟨fun h ↦ h (), fun h u ↦ by cases u; exact h⟩
  let σ : Fin (n k₀ + 1) → Coord (fun _ : Unit ↦ n k₀) := fun i ↦ ⟨(), i⟩
  let τ : Coord (fun _ : Unit ↦ n k₀) → Fin (n k₀ + 1) := fun v ↦ v.2
  have hev : ∀ f, eval₂ (Int.castRingHom ℂ) (w ()) f = evalCone w (rename σ f) := by
    intro f
    rw [evalCone, eval₂_rename]
    rfl
  have hev' : ∀ f, evalCone w f = eval₂ (Int.castRingHom ℂ) (w ()) (rename τ f) := by
    intro f
    rw [evalCone, eval₂_rename]
    congr 1
  simp only [GroundTheory.Heights₂.Heights.conePoints, oneBlockPoints, Set.mem_ofPred_eq]
  rw [hw0]
  refine and_congr_right fun _ ↦ ⟨fun h f hf ↦ ?_, fun h f hf ↦ ?_⟩
  · rw [hev]
    apply h
    rw [ArithVariety.projIdeal, Ideal.mem_comap, rename_rename]
    exact Ideal.mem_comap.1 hf
  · rw [hev']
    apply h
    rw [oneBlockIdeal, Ideal.mem_comap, rename_rename]
    exact Ideal.mem_comap.1 hf
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
