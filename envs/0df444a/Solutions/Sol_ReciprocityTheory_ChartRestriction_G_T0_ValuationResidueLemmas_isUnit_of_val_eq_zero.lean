-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.isUnit_of_val_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:36:23.569072+00:00
-- url     : https://prove2.me/submissions/0cc5267c-bfd4-41f6-acbf-a747d8043109

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
namespace ValuationResidueLemmas
section
variable {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
private lemma mem_iff_lemma (y : F) : y ∈ vRing v ↔ 0 ≤ v y := by
  first
    | exact Iff.rfl
    | exact Valuation.mem_valuationSubring_iff _ _
end
end ValuationResidueLemmas
namespace ValuationResidueLemmas
end ValuationResidueLemmas
namespace ValuationResidueLemmas
end ValuationResidueLemmas
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
variable {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
namespace ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
theorem _root_.solution (x : vRing v) (hx : v (x : F) = 0) : IsUnit x := by
  have hx0 : (x : F) ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hx
    simp at hx
  have h2 : v ((x : F)⁻¹) = 0 := by
    have h3 := AddValuation.map_mul v ((x : F)⁻¹) x
    rw [inv_mul_cancel₀ hx0, AddValuation.map_one, hx, add_zero] at h3
    exact h3.symm
  have hinv : (x : F)⁻¹ ∈ vRing v := (mem_iff_lemma v _).2 (le_of_eq h2.symm)
  have hmul : x * ⟨(x : F)⁻¹, hinv⟩ = 1 := by
    apply Subtype.ext
    show (x : F) * (x : F)⁻¹ = 1
    exact mul_inv_cancel₀ hx0
  first
    | exact IsUnit.of_mul_eq_one _ hmul
    | exact isUnit_of_mul_eq_one x _ hmul
    | exact ⟨⟨x, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
end ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
