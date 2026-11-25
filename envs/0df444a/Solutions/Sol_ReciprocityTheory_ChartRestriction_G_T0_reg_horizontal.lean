-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.reg_horizontal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:32:02.202985+00:00
-- url     : https://prove2.me/submissions/466faa7b-9e05-4767-81f6-33957dd25ffd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegHorPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegHor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_reg_horizontal_pf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    (P : Ideal A) [P.IsPrime] (hh : ¬ Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P)
    (hmeet : P ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤) (e : A) (he : e ≠ 0)
    (f : FractionRing A)
    (hdvr : (¬ ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) →
      ∃ a s : A, a ∈ P ∧ s ∉ P ∧ f⁻¹ * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 → φ e ≠ 0 →
      ∃ v : V, φ a = v * φ b) :
    ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  exact reg_horizontal_pf P hh hmeet e he f hdvr hf
end ReciprocityTheory.ChartRestriction.G.T0
