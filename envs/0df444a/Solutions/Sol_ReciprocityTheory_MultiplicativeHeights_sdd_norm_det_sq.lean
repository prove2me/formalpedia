-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_norm_det_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:14.627269+00:00
-- url     : https://prove2.me/submissions/4c8da52b-2f0e-4f78-b8ca-cead7e1c9c0d

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    (Bᴴ * B).det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_mul, det_conjTranspose, Complex.star_def, Complex.conj_mul']
  push_cast
  ring
end ReciprocityTheory.MultiplicativeHeights
