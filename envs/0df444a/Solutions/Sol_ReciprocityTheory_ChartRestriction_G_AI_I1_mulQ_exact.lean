-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.mulQ_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:27:37.036215+00:00
-- url     : https://prove2.me/submissions/46bd827e-8600-4ac9-af26-97415d36a2ba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero

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
theorem _root_.solution (V : Ideal R) (f g : R) :
    Function.Exact (mulQ V f g) (Submodule.factor (sup_span_mul_le V f g)) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change (Submodule.Quotient.mk y : R ⧸ (V ⊔ Ideal.span {f})) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hy
    obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    rw [mulQ, Submodule.mapQ_apply, Submodule.Quotient.eq]
    simp only [LinearMap.mulLeft_apply]
    have : f * c - y = -v := by linear_combination hvw
    rw [this]
    exact Submodule.neg_mem _ (Ideal.mem_sup_left hv)
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [mulQ, Submodule.mapQ_apply, LinearMap.mulLeft_apply, Submodule.Quotient.eq] at hx
    have h1 := sup_span_mul_le V f g hx
    have h2 : f * x ∈ V ⊔ Ideal.span {f} :=
      Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))
    have e : y = f * x - (f * x - y) := by ring
    rw [e]
    exact Submodule.sub_mem _ h2 h1
end ReciprocityTheory.ChartRestriction.G.AI.I1
