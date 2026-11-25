-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:26.445854+00:00
-- url     : https://prove2.me/submissions/1f8aeacc-44bf-43f4-823a-3afd48d87ebb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_length_quot_maximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution [IsDomain R] (x : R) (hx : x ≠ 0) [(Ideal.span {x}).IsPrime] (m : ℕ) :
    Module.length (Localization.AtPrime (Ideal.span {x}))
      (Localization.AtPrime (Ideal.span {x}) ⧸
        (Ideal.span {x ^ m}).map (algebraMap R (Localization.AtPrime (Ideal.span {x})))) = m := by
  set A := Localization.AtPrime (Ideal.span {x})
  have hinj : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A (Ideal.span {x}).primeCompl_le_nonZeroDivisors
  have : IsDomain A := inferInstance
  have hx' : algebraMap R A x ∈ nonZeroDivisors A :=
    mem_nonZeroDivisors_of_ne_zero fun h => hx (hinj (by rw [h, map_zero]))
  rw [Ideal.map_span, Set.image_singleton, map_pow]
  change Ring.ord A (algebraMap R A x ^ m) = m
  rw [Ring.ord_pow hx', Ring.ord, ← Set.image_singleton, ← Ideal.map_span,
    inh_length_quot_maximal]
  simp
end ReciprocityTheory.ChartRestriction.G.AI.I1
