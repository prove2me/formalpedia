-- Prove2me | solution 1 for ReciprocityTheory.PGsh.linSub_cayDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:49.210099+00:00
-- url     : https://prove2.me/submissions/36c80789-7bca-42fe-bd11-51dc2b88980c

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
theorem _root_.solution (g : Matrix (Fin n) (Fin n) R) :
    linSub g (cayDet n R) = C g.det * cayDet n R := by
  show linSub g (Matrix.mvPolynomialX (Fin n) (Fin n) R).det = _
  rw [AlgHom.map_det]
  have e : (linSub g).mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) R) =
      (C : R →+* MvPolynomial (Fin n × Fin n) R).mapMatrix g *
        Matrix.mvPolynomialX (Fin n) (Fin n) R := by
    ext i j
    simp [linSub, Matrix.mul_apply]
  rw [e, Matrix.det_mul, ← RingHom.map_det]
end ReciprocityTheory.PGsh
