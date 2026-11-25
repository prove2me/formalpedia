-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mul_mem_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:11:59.51542+00:00
-- url     : https://prove2.me/submissions/c5376a4c-2c65-48e0-bf2d-82c8cc1ad7dd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsMPrimeFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_RelIndexNeZeroOfMulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Module
variable {Ω : Type} [Field Ω] [CharZero Ω]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {S S' : Submodule ℤ Ω} {M : Ω} (hM : ∀ u ∈ S', M * u ∈ S) (A : Submodule ℤ Ω) :
    ∀ u ∈ A * S', M * u ∈ A * S := by
  intro u hu
  refine Submodule.mul_induction_on hu (fun a ha b hb => ?_) (fun y z hy hz => ?_)
  · rw [mul_left_comm]
    exact Submodule.mul_mem_mul ha (hM b hb)
  · rw [mul_add]
    exact add_mem hy hz
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
