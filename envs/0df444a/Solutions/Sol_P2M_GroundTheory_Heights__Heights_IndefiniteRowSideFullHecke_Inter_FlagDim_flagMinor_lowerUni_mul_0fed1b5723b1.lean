-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_flagMinor_lowerUni_mul_0fed1b5723b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:13:14.557197+00:00
-- url     : https://prove2.me/submissions/77b533e0-8f85-48e2-a8fe-ffcab4245c3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (E M : Matrix (Fin n) (Fin n) R)
    (hE : ∀ i k, i < k → E i k = 0) (hE1 : ∀ i, E i i = 1) (j : Fin (n - 1)) (S : PluckerBlocks n n j) :
    flagMinor (E * M) j S = flagMinor M j S := by
  have hj := j.2
  simp only [flagMinor]
  have key : (E * M).submatrix (Fin.castLE (by omega) : Fin (j.val + 1) → Fin n) (S.1.orderEmbOfFin S.2) =
      E.submatrix (Fin.castLE (by omega) : Fin (j.val + 1) → Fin n) (Fin.castLE (by omega)) *
        M.submatrix (Fin.castLE (by omega) : Fin (j.val + 1) → Fin n) (S.1.orderEmbOfFin S.2) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE (by omega)) (Fin.castLE_injective _) _ _ ?_ ?_
    · intro k hk
      have hk' : ¬ k.val < j.val + 1 := fun h => hk ⟨⟨k.val, h⟩, rfl⟩
      rw [hE _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; omega), zero_mul]
    · intro k
      rfl
  rw [key, Matrix.det_mul, Matrix.det_of_isLowerTriangular, Finset.prod_eq_one, one_mul]
  · intro i _
    simp [hE1]
  · intro a b hab
    simp only [Matrix.submatrix_apply]
    apply hE
    simp only [OrderDual.toDual_lt_toDual] at hab
    simp only [Fin.lt_def, Fin.val_castLE] at hab ⊢
    exact hab
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
