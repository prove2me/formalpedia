-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_quot_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:42.054985+00:00
-- url     : https://prove2.me/submissions/9a7cc2f9-dad1-467e-b858-c85d7c2f6f1c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_locLen_eq_zero_of_notMem


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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution {V : Ideal R} {g : R} (p : PrimeSpectrum R) (hg : g ∉ p.asIdeal) :
    locLen (R ⧸ (V ⊔ Ideal.span {g})) p = 0 := by
  refine locLen_eq_zero_of_notMem p fun hp => hg ?_
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient, PrimeSpectrum.mem_zeroLocus] at hp
  exact hp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
end ReciprocityTheory.ChartRestriction.G.AI.I1
