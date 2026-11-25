-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.val_eq_zero_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:37:04.70297+00:00
-- url     : https://prove2.me/submissions/1af0198d-477c-463a-91df-e65fb3435af8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_wt_add_eq_zero
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
theorem _root_.solution (x : vRing v) (hx : IsUnit x) : v (x : F) = 0 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have hxy : (x : F) * (y : F) = 1 := by
    have h1 := congrArg (fun z : vRing v => (z : F)) hy
    simpa using h1
  have h1 : v ((x : F) * (y : F)) = 0 := by
    rw [hxy, AddValuation.map_one]
  rw [AddValuation.map_mul] at h1
  exact wt_add_eq_zero ((mem_iff_lemma v _).1 x.2) ((mem_iff_lemma v _).1 y.2) h1
end ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
