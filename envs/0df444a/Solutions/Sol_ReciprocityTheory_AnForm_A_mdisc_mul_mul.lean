-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:09.07193+00:00
-- url     : https://prove2.me/submissions/d2eb8b0e-525b-4779-834d-673d9ccaf600

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (B C : Matrix (Fin D) (Fin D) ℂ) (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc (fun k => B * A k * C) = B.det * C.det * mdisc A := by
  unfold mdisc
  have h : ∀ S : Finset (Fin D),
      (∑ k ∈ S, B * A k * C).det = B.det * C.det * (∑ k ∈ S, A k).det := by
    intro S
    rw [← Finset.sum_mul, ← Finset.mul_sum, Matrix.det_mul, Matrix.det_mul]
    ring
  simp_rw [h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by ring
end ReciprocityTheory.AnForm.A
