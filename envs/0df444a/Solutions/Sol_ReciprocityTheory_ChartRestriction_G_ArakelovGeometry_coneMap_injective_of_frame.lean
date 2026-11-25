-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.coneMap_injective_of_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:13.502548+00:00
-- url     : https://prove2.me/submissions/b1ea2d1f-41d7-4256-a8c1-b88f79b12619

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemSec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e) :
    Function.Injective (coneMap ℤ (v ∘ e)) := by
  exact (injective_iff_map_eq_zero _).2 fun p hp => by
    have h : p ∈ coordIdeal ℤ (v ∘ e) := (RingHom.mem_ker).2 hp
    rwa [hf.free, Ideal.mem_bot] at h
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
