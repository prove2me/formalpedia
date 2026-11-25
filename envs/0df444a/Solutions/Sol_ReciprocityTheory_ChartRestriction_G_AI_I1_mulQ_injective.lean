-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.mulQ_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:27:39.170188+00:00
-- url     : https://prove2.me/submissions/c0827973-9041-4a5c-b23f-73d22aaa3805

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
theorem _root_.solution {V : Ideal R} (hV : V.IsPrime) {f : R} (hf : f ∉ V) (g : R) :
    Function.Injective (mulQ V f g) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker, mulQ, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
  have h1 : f * (x - c * g) ∈ V := by
    have : f * (x - c * g) = v := by
      simp only [LinearMap.mulLeft_apply] at hvw
      linear_combination -hvw
    rw [this]; exact hv
  have h2 : x - c * g ∈ V := (hV.mem_or_mem h1).resolve_left hf
  have : x = (x - c * g) + c * g := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mem_sup_left h2)
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))
end ReciprocityTheory.ChartRestriction.G.AI.I1
