-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_latticePoint_mem_5d2a33e3dc3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:00.143076+00:00
-- url     : https://prove2.me/submissions/4c7562b5-532c-4959-903a-0ab6caca9b70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_latticePoint_ne_zero_40cbc107ef6e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) (σ : K →+* ℂ) {w : Fin (r + 1) → ℂ} (hw : w ≠ 0) :
    latticePoint φ σ w ∈ conePoints (latticeIdeal φ) ℂ := by
  refine ⟨fun _ ↦ latticePoint_ne_zero hφ σ hw, fun f hf ↦ ?_⟩
  have hf' : latticeMap φ f = 0 := hf
  have key : (eval₂Hom (Int.castRingHom ℂ) fun v : Coord (fun _ : Unit ↦ N) ↦ latticePoint φ σ w v.1 v.2) =
      (eval w).comp ((map σ).comp (latticeMap φ)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro v; simp [latticeMap, latticeForm, latticePoint]
  have h := congrArg (fun g ↦ g f) key
  simp only [RingHom.comp_apply, hf', map_zero] at h
  exact h
end GroundTheory.Heights₂.Heights
