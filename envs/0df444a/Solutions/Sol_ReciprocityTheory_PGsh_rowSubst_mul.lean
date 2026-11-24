-- Prove2me | solution 1 for ReciprocityTheory.PGsh.rowSubst_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:19:15.764367+00:00
-- url     : https://prove2.me/submissions/4fd16464-0b2f-46ba-a2ce-a70793302ece

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
theorem _root_.solution (g h : Matrix (Fin ν) (Fin ν) ℂ) (P : MvPolynomial (Fin ν × ι) ℂ) :
    rowSubst h (rowSubst g P) = rowSubst (h * g) P := by
  have key : (rowSubst (ι := ι) h).comp (rowSubst g) = rowSubst (h * g) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, rowSubst, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, MvPolynomial.C_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  exact congrArg (fun F => F P) key
end ReciprocityTheory.PGsh
