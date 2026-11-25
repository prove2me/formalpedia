-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_coord_decomp_f25ef847aa3c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:42:12.381502+00:00
-- url     : https://prove2.me/submissions/4da790c3-950a-4922-b5b1-52f895dc8ce0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemIdealLattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_sumBasis_apply_2327b92b9453


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ComplexAt
open scoped nonZeroDivisors ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6 GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
theorem _root_.solution {n m k : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (b : Fin m → Fin n → K)
    (c : Fin k → Fin n → K) (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n)
    (σ : K →+* ℂ) (x : Fibre σ (idealLattice a)) :
    ∃ β : Fin m → ℂ, latticeCoord σ (idealLattice a) x =
      embMat σ (Sum.elim b c) *ᵥ Sum.elim β (latticeCoord σ (quotLattice a b c hli hmk)
        ((quotProj a b c hli hmk).lTensor (ComplexAt σ) x)) := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul z v =>
    refine ⟨fun i => σ ((sumBasis b c hli hmk).repr v (Sum.inl i)) * (ofComplex σ).symm z, ?_⟩
    have hu : Sum.elim (fun i => σ ((sumBasis b c hli hmk).repr v (Sum.inl i)) *
        (ofComplex σ).symm z) (latticeCoord σ (quotLattice a b c hli hmk)
          ((quotProj a b c hli hmk).lTensor (ComplexAt σ) (z ⊗ₜ v))) =
        fun s => σ ((sumBasis b c hli hmk).repr v s) * (ofComplex σ).symm z := by
      funext s
      rcases s with i | j
      · rfl
      · rw [Sum.elim_inr, LinearMap.lTensor_tmul, latticeCoord_tmul]
        rfl
    rw [hu]
    funext r
    rw [latticeCoord_tmul]
    have hv := congrFun ((sumBasis b c hli hmk).sum_repr (v : Fin n → K)) r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sumBasis_apply] at hv
    simp only [mulVec, dotProduct, embMat, of_apply]
    rw [← hv, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_mul]
    ring
  | add x y hx hy =>
    obtain ⟨β, hβ⟩ := hx
    obtain ⟨β', hβ'⟩ := hy
    refine ⟨β + β', ?_⟩
    rw [map_add, map_add, map_add, hβ, hβ', ← mulVec_add, Sum.elim_add_add]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
