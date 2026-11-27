-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S9_hypotheses_inhabited_1ae21cf550ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:58:55.527926+00:00
-- url     : https://prove2.me/submissions/f947fcfa-c274-4723-a978-b3fde4848b6f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExtendedDataRemainder

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S9
theorem _root_.solution :
    4 * ((1 : ℕ) : ℝ) * ((1 + 1 : ℕ) : ℝ) ^ 2 ≤ 16 ∧
      IsPsumDecomposition 1 (1 + 1) (restPoly 1 1 1 .last) inhQ ∧
      ∀ (p n' : ℕ) (τ : Fin 1) (k : ℕ), (fun _ _ _ _ => (1 : ℚ)) p n' τ k = 1 ∨
        (fun _ _ _ _ => (1 : ℚ)) p n' τ k = -1 := by
  refine ⟨by norm_num, ?_, fun _ _ _ _ => Or.inl rfl⟩
  have hI : Finset.Icc 1 (1 + 1) = ({1, 2} : Finset ℕ) := by decide
  simp only [IsPsumDecomposition, restPoly, smallMu, fibClass, alternant, smallRoots,
    otherRoots, hI, inhQ, blockPsum, Matrix.det_unique, Finset.univ_unique, Finset.sum_singleton,
    Finset.prod_singleton]
  rw [Finset.sum_pair (by norm_num)]
  simp [staircase, Fin.sum_univ_succ]
  have h2 : (C (2⁻¹ : ℚ) : RootPoly 1 (1 + 1)) * 2 = 1 := by
    rw [show (2 : RootPoly 1 (1 + 1)) = C 2 from (map_ofNat C 2).symm, ← C_mul]; norm_num
  linear_combination (-X ((0 : Fin 1), (1 : Fin (1 + 1))) ^ 2) * h2
end S9
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
