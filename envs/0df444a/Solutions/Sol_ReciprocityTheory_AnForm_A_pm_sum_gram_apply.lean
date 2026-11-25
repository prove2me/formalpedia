-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.pm_sum_gram_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:52.662458+00:00
-- url     : https://prove2.me/submissions/94309293-e4ef-42d6-951f-056925ce0593

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Finset
open scoped ComplexOrder
variable {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (w : Fin D → ι → Fin D → ℂ) (S : Finset (Fin D)) (a b : Fin D) :
    (∑ k ∈ S, pmGram w k) a b =
      ∑ p : Fin D × ι, (if p.1 ∈ S then (1 : ℂ) else 0) * (w p.1 p.2 a * star (w p.1 p.2 b)) := by
  simp only [Matrix.sum_apply, pmGram, Matrix.of_apply, Fintype.sum_prod_type, ite_mul, one_mul,
    zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun x _ hx => by simp [hx])]
  exact Finset.sum_congr rfl fun x hx => by simp [hx]
end ReciprocityTheory.AnForm.A
