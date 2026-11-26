-- Prove2me | solution 1 for closure_numericalRange_eq_empty_iff_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:31:45.156885+00:00
-- url     : https://prove2.me/submissions/f3b2dbdb-4a15-4041-b2e7-07d1fd322c85

import Mathlib.Analysis.Normed.Module.Normalize
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Nonempty
import Theorems.Thm_closure_numericalRange_nonempty_iff_nontrivial

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) :
    closure (numericalRange A) = ∅ ↔ Subsingleton E := by
  rw [← Set.not_nonempty_iff_eq_empty,
    closure_numericalRange_nonempty_iff_nontrivial,
    not_nontrivial_iff_subsingleton]
