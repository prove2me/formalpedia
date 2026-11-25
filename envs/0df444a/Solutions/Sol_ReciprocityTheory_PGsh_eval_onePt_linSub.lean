-- Prove2me | solution 1 for ReciprocityTheory.PGsh.eval_onePt_linSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:46:13.36907+00:00
-- url     : https://prove2.me/submissions/d264f819-314d-4cee-b1a9-cff9712434e7

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
theorem _root_.solution (x : Fin n × Fin n → ℤ) (p : MvPolynomial (Fin n × Fin n) ℤ) :
    eval onePt (linSub (Matrix.of fun i j => x (i, j)) p) = eval x p := by
  have e : (eval onePt).comp (linSub (Matrix.of fun i j => x (i, j))).toRingHom = eval x := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [linSub]
    · intro v
      simp [linSub, onePt, Matrix.one_apply]
  exact RingHom.congr_fun e p
end ReciprocityTheory.PGsh
