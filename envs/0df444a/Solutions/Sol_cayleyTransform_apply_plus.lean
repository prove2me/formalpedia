-- Prove2me | solution 1 for cayleyTransform_apply_plus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:40.386686+00:00
-- url     : https://prove2.me/submissions/02e5d453-a7f0-4cd7-b89b-6feab02a1cda

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Definitions.Def_Spectral_Cayley_Basic

set_option autoImplicit false
open scoped LinearPMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (x : A.domain) :
    cayleyTransform A hA (A x + Complex.I • (x : E)) =
      A x - Complex.I • (x : E) := by
  let e := LinearEquiv.ofBijective (plusI A) ⟨plusI_injective A hA, plusI_surjective A hA⟩
  change minusI A (e.symm (plusI A x)) = minusI A x
  change minusI A (e.symm (e x)) = minusI A x
  rw [e.symm_apply_apply]
