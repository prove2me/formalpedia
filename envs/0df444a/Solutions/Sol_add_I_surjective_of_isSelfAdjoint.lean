-- Prove2me | solution 1 for add_I_surjective_of_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:41.451418+00:00
-- url     : https://prove2.me/submissions/bfa35fa2-3128-4b14-8275-9c7574e376bf

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Definitions.Def_Spectral_Cayley_Basic

set_option autoImplicit false
open scoped LinearPMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    Function.Surjective (fun x : A.domain => A x + Complex.I • (x : E)) := by
  exact plusI_surjective A hA
