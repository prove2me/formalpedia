-- Prove2me | solution 1 for ReciprocityTheory.PGsh.eval_cayDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:46:10.83507+00:00
-- url     : https://prove2.me/submissions/fbaae776-d108-4949-8d75-9fb7bc403658

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
namespace ReciprocityTheory.PGsh
theorem _root_.solution (x : Fin n × Fin n → ℤ) :
    eval x (cayDet n ℤ) = (Matrix.of fun i j => x (i, j)).det := by
  show eval x (Matrix.mvPolynomialX (Fin n) (Fin n) ℤ).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp
end ReciprocityTheory.PGsh
