-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMinorsBaseChange_flagMinor_mul_const_mem_d361f6596ffb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:49.130652+00:00
-- url     : https://prove2.me/submissions/2b0bb1b8-7002-473e-8fda-bdd8959b9e14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinet_proof_066722d63378


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMinorsBaseChange
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMinorsBaseChange
theorem _root_.solution {F : Type} [Field F] {σ : Type} {n m p : ℕ}
    (M : Matrix (Fin n) (Fin m) (MvPolynomial σ F)) (D : Matrix (Fin m) (Fin p) F)
    (N : Matrix (Fin n) (Fin p) (MvPolynomial σ F)) (hN : ∀ a b, N a b = ∑ k, M a k * C (D k b))
    (j : Fin (n - 1)) (S : PluckerBlocks p n j) :
    flagMinor N j S ∈
      Algebra.adjoin F (Set.range fun q : Σ j, PluckerBlocks m n j => flagMinor M q.1 q.2) := by
  have hle : (j : ℕ) + 1 ≤ n := by have := j.2; omega
  have hsplit : N.submatrix (Fin.castLE hle) (S.1.orderEmbOfFin S.2) =
      (M.submatrix (Fin.castLE hle) id : Matrix (Fin ((j : ℕ) + 1)) (Fin m) (MvPolynomial σ F)) *
        ((D.map (C : F → MvPolynomial σ F)).submatrix id (S.1.orderEmbOfFin S.2) :
          Matrix (Fin m) (Fin ((j : ℕ) + 1)) (MvPolynomial σ F)) := by
    ext a b
    rw [Matrix.submatrix_apply, hN, Matrix.mul_apply]
    rfl
  unfold flagMinor
  rw [hsplit, GroundTheory.Heights₂.Heights.CauchyBinet.proof]
  refine Subalgebra.sum_mem _ fun I _ => Subalgebra.mul_mem _ ?_ ?_
  · apply Algebra.subset_adjoin
    exact ⟨⟨j, I⟩, rfl⟩
  · have h : rowsOf ((D.map (C : F → MvPolynomial σ F)).submatrix id (S.1.orderEmbOfFin S.2)) I =
        (RingHom.mapMatrix (C : F →+* MvPolynomial σ F))
          (D.submatrix (I.1.orderEmbOfFin I.2) (S.1.orderEmbOfFin S.2)) := by
      ext a b
      rfl
    rw [h, ← RingHom.map_det]
    exact Subalgebra.algebraMap_mem _ _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMinorsBaseChange
