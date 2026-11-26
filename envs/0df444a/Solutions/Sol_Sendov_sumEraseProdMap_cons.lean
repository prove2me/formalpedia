-- Prove2me | solution 1 for Sendov.sumEraseProdMap_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:55:46.528408+00:00
-- url     : https://prove2.me/submissions/8ad8f2f8-8959-4c25-b790-932d427f6a0b

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open scoped Classical
namespace Sendov
theorem _root_.solution {α : Type*} (v : α) (t : Multiset α) (f : α → ℝ) :
    sumEraseProdMap (v ::ₘ t) f = (t.map f).prod + f v * sumEraseProdMap t f := by
  simp only [sumEraseProdMap, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro j hj
  rw [Multiset.erase_cons_tail_of_mem hj, Multiset.map_cons, Multiset.prod_cons]
end Sendov
