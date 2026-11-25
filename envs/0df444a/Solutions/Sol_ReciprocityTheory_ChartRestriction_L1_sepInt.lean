-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.sepInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:45:27.589714+00:00
-- url     : https://prove2.me/submissions/013ed687-c206-41dc-b2ba-06ea408e9b63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModSepInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_exists_int_multiple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_mem_valuationSubring_of_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {Ω : Type*} [Field Ω] [CharZero Ω] (s : Finset Ω) (hs : ∀ r ∈ s, IsIntegral ℤ r) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → ∀ A : ValuationSubring Ω, r - r' ∈ A.nonunits →
      (n : Ω) ∈ A.nonunits := by
  classical
  have key : ∀ q ∈ s.offDiag, ∃ (m : ℤ) (γ : Ω), m ≠ 0 ∧ IsIntegral ℤ γ ∧ (m : Ω) = (q.1 - q.2) * γ := by
    intro q hq
    rw [Finset.mem_offDiag] at hq
    exact exists_int_multiple ((hs _ hq.1).sub (hs _ hq.2.1)) (sub_ne_zero.2 hq.2.2)
  choose! m γ hm hγ hmγ using key
  refine ⟨∏ q ∈ s.offDiag, m q, Finset.prod_ne_zero_iff.2 hm, ?_⟩
  intro r hr r' hr' hne A hA
  have hq : (r, r') ∈ s.offDiag := Finset.mem_offDiag.2 ⟨hr, hr', hne⟩
  rw [Int.cast_prod, ← Finset.mul_prod_erase _ _ hq]
  rw [ValuationSubring.mem_nonunits_iff] at hA ⊢
  rw [Valuation.map_mul, hmγ _ hq, Valuation.map_mul]
  have h1 : A.valuation (γ (r, r')) ≤ 1 :=
    (A.valuation_le_one_iff _).2 (mem_valuationSubring_of_isIntegral (hγ _ hq) A)
  have h2 : A.valuation (∏ q ∈ s.offDiag.erase (r, r'), (m q : Ω)) ≤ 1 :=
    (A.valuation_le_one_iff _).2 (prod_mem fun q _ => intCast_mem _ _)
  calc _ ≤ A.valuation (r - r') * 1 * 1 := mul_le_mul' (mul_le_mul' le_rfl h1) h2
    _ < 1 := by rw [mul_one, mul_one]; exact hA
end ReciprocityTheory.ChartRestriction.L1
