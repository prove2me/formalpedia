-- Prove2me | solution 1 for ReciprocityTheory.PGsh.funMat_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:45:34.864838+00:00
-- url     : https://prove2.me/submissions/c030d3a3-25f5-45ec-a76c-a4c475ad21f6

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
theorem _root_.solution : funMat (fun b : Fin n => b) = 1 := by
  ext a b
  simp [funMat, Matrix.one_apply]
end ReciprocityTheory.PGsh
