-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.mem_max_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:42:49.866999+00:00
-- url     : https://prove2.me/submissions/ac2c6ff4-4d22-4408-96d5-5f0dc1d6ac45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_val_eq_zero_of_isUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_isUnit_of_val_eq_zero
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
theorem _root_.solution (x : vRing v) : x ∈ maximalIdeal (vRing v) ↔ 0 < v (x : F) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have h0 : 0 ≤ v (x : F) := (mem_iff_lemma v _).1 x.2
  constructor
  · intro h
    exact lt_of_le_of_ne h0 (fun he => h (isUnit_of_val_eq_zero v x he.symm))
  · intro h hu
    exact h.ne' (val_eq_zero_of_isUnit v x hu)
end ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
