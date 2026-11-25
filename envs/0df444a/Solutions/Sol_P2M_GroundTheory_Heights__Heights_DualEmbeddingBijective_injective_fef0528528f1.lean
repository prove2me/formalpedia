-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_injective_fef0528528f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:40.023061+00:00
-- url     : https://prove2.me/submissions/44f59b68-74c9-4033-b8bf-f58c06a013ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualEmbBijective
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_exists_zsmul_mem_dualLattice_a99542587a2d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_pairing_single_4a952709d21e

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
open NumberField Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.DualEmbeddingBijective
variable {K : Type} [Field K] [NumberField K] {i : ℕ}
namespace GroundTheory.Heights₂.Heights.DualEmbeddingBijective
theorem _root_.solution (F : HermLattice K i) {T : Type} [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice F)) :
    Function.Injective (Matrix.mulVecLin (dualEmbMatrix b)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have hb : ∀ t, pairing w (b t : Fin i → K) = 0 := fun t => by
    have h := congrFun hw t
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, dualEmbMatrix, pairing] using h
  have hL : ∀ φ : dualLattice F, pairing w φ = 0 := by
    intro φ
    rw [← b.sum_repr φ, Submodule.coe_sum, map_sum]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [Submodule.coe_smul, map_zsmul, hb, smul_zero]
  have hK : ∀ y, pairing w y = 0 := by
    intro y
    obtain ⟨N, hN, hy⟩ := exists_zsmul_mem_dualLattice F y
    have h := hL ⟨_, hy⟩
    rw [Submodule.coe_mk, map_zsmul] at h
    exact (smul_eq_zero.mp h).resolve_left hN
  funext p
  obtain ⟨σ, j⟩ := p
  have hli := (linearIndependent_monoidHom K ℂ).comp (fun σ : K →+* ℂ => σ.toMonoidHom)
    (fun σ τ h => RingHom.ext fun x => DFunLike.congr_fun h x)
  rw [Fintype.linearIndependent_iff] at hli
  refine hli (fun σ => w (σ, j)) ?_ σ
  funext x
  have h := hK (Pi.single j x)
  rw [pairing_single] at h
  simpa [Finset.sum_apply] using h
end GroundTheory.Heights₂.Heights.DualEmbeddingBijective
