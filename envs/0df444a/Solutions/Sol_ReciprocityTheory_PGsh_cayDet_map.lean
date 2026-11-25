-- Prove2me | solution 1 for ReciprocityTheory.PGsh.cayDet_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:34:22.943874+00:00
-- url     : https://prove2.me/submissions/6eba3078-57c8-4d00-ade7-94711aa3978a

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.PGsh
theorem _root_.solution : map (Int.castRingHom R) (cayDet n ℤ) = cayDet n R := by
  show map (Int.castRingHom R) (Matrix.mvPolynomialX (Fin n) (Fin n) ℤ).det =
    (Matrix.mvPolynomialX (Fin n) (Fin n) R).det
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mvPolynomialX_apply, map_X]
end ReciprocityTheory.PGsh
