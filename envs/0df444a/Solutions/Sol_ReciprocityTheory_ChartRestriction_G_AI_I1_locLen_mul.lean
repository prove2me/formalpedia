-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:36:17.977792+00:00
-- url     : https://prove2.me/submissions/c8b13a7f-ea37-40a0-b17f-23aa19f500f1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_mulQ_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_mulQ_exact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_locLen_add


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
theorem _root_.solution {V : Ideal R} (hV : V.IsPrime) {f : R} (hf : f ∉ V) (g : R) (p : PrimeSpectrum R) :
    locLen (R ⧸ (V ⊔ Ideal.span {f * g})) p =
      locLen (R ⧸ (V ⊔ Ideal.span {g})) p + locLen (R ⧸ (V ⊔ Ideal.span {f})) p :=
  locLen_add _ _ (mulQ_injective hV hf g) (Submodule.factor_surjective _) (mulQ_exact V f g) p
end ReciprocityTheory.ChartRestriction.G.AI.I1
