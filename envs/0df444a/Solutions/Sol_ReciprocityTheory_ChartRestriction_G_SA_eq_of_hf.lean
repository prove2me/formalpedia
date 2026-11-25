-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.eq_of_hf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:33:18.786984+00:00
-- url     : https://prove2.me/submissions/e113b64a-8ad5-49a4-a677-48444a0c701b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] (σ : R →+* R)
  (J : Matrix ι ι R)
variable {σ J}
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (M M' : Matrix ι ι R) (h : ∀ x y, hf σ M x y = hf σ M' x y) : M = M' := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rwa [hf_single, hf_single] at this
end ReciprocityTheory.ChartRestriction.G.SA
