-- Prove2me | solution 1 for ReciprocityTheory.PGsh.rowSubst_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:19:17.418836+00:00
-- url     : https://prove2.me/submissions/c3ddbd09-75fa-4ca5-9d08-9b419b1b38a8

import Definitions.Def_ReciprocityTheory_DualLattices_WtGtRowSubstXSub
import Definitions.Def_ReciprocityTheory_DualLattices_FischerSelfNeZero

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
open scoped Classical
open ReciprocityTheory ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (P : MvPolynomial (Fin ν × ι) ℂ) : rowSubst (1 : Matrix (Fin ν) (Fin ν) ℂ) P = P := by
  have h : (fun p : Fin ν × ι => ∑ l, C ((1 : Matrix (Fin ν) (Fin ν) ℂ) l p.1) * X (l, p.2)) = X := by
    funext p
    rw [Finset.sum_eq_single p.1]
    · simp
    · intro l _ hl
      simp [Matrix.one_apply_ne hl]
    · simp
  unfold rowSubst
  rw [h, MvPolynomial.aeval_X_left_apply]
end ReciprocityTheory.PGsh
