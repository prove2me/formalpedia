-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.residue_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:55:26.774394+00:00
-- url     : https://prove2.me/submissions/d11d657e-bdc6-4eec-9afe-fef538a0308b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_mem_max_iff
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
theorem _root_.solution (x : vRing v) : residue (vRing v) x ≠ 0 ↔ v (x : F) = 0 := by
  rw [Ne, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
  have h0 : 0 ≤ v (x : F) := (mem_iff_lemma v _).1 x.2
  constructor
  · intro h
    exact (eq_of_le_of_not_lt h0 h).symm
  · intro h hlt
    rw [h] at hlt
    exact lt_irrefl _ hlt
end ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
