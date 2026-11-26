-- Prove2me | solution 1 for closure_numericalRange_nonempty_iff_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:18:56.954804+00:00
-- url     : https://prove2.me/submissions/ac564702-2aa4-4a13-8108-53db224f8dd0

import Mathlib.Analysis.Normed.Module.Normalize
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Nonempty
import Theorems.Thm_numericalRange_nonempty_iff_nontrivial

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) :
    (closure (numericalRange A)).Nonempty ↔ Nontrivial E :=
  closure_nonempty_iff.trans (numericalRange_nonempty_iff_nontrivial A)
