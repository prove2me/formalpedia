-- Prove2me | solution 1 for ReciprocityTheory.PGsh.det_funMat_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:07:48.663507+00:00
-- url     : https://prove2.me/submissions/75ef62b6-b49a-4549-9fc2-b07a925a5453

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
theorem _root_.solution (σ : Equiv.Perm (Fin n)) : (funMat σ).det = Equiv.Perm.sign σ := by
  have e : funMat σ = (σ.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) ℤ)ᵀ := by
    ext a b
    by_cases h : a = σ b
    · simp [funMat, PEquiv.toMatrix_apply, h]
    · have h' : σ b ≠ a := fun e => h e.symm
      simp [funMat, PEquiv.toMatrix_apply, h, h']
  rw [e, Matrix.det_transpose]
  simp [Matrix.det_permutation]
end ReciprocityTheory.PGsh
