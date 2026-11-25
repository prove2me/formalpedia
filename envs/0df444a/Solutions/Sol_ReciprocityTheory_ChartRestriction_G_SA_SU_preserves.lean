-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.SU_preserves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:45:37.71708+00:00
-- url     : https://prove2.me/submissions/29a95d33-b33f-4a37-9201-cca9156e0b84

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_mem_SU_iff

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
theorem _root_.solution {g : Matrix ι ι R} (hg : g ∈ SU σ J) (x y : ι → R) :
    hf σ J (g *ᵥ x) (g *ᵥ y) = hf σ J x y :=
  ((mem_SU_iff g).1 hg).2 x y
end ReciprocityTheory.ChartRestriction.G.SA
