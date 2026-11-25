-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassmannianArithmeticVariety_minor_idx_ae6f2d509457
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:04.054014+00:00
-- url     : https://prove2.me/submissions/2a0f0943-7a32-4d07-975d-1de23fe27be9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianArithmeticVariety_det_submatrix_sign_ed8aebb8ad35

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.GrassmannianArithmeticVariety
namespace GroundTheory.Heights₂.Heights.GrassmannianArithmeticVariety
theorem _root_.solution {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R)
    (a : Fin j) (b : Fin m) :
    ∃ s : ℤˣ, (colsOf (onePipe Z) (idx a b)).det = ((s : ℤ) : R) * Z a b := by
  obtain ⟨s, hs⟩ := det_submatrix_sign (onePipe Z) (col a b) _ (col_injective a b)
    ((idx a b).1.orderEmbOfFin (idx a b).2).injective (by
      rw [Finset.range_orderEmbOfFin]; simp [idx])
  refine ⟨s, ?_⟩
  have hcol : (onePipe Z).submatrix id (col a b) = (1 : Matrix (Fin j) (Fin j) R).updateCol a
      (fun r => Z r b) := by
    ext r i
    by_cases hi : i = a
    · simp [col, onePipe, hi]
    · simp [col, onePipe, hi]
  rw [colsOf, hs, hcol, ← cramer_apply, cramer_one]
  rfl
end GroundTheory.Heights₂.Heights.GrassmannianArithmeticVariety
