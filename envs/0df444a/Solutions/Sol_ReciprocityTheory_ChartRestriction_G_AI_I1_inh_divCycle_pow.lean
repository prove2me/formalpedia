-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_divCycle_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:06.992363+00:00
-- url     : https://prove2.me/submissions/58d272d4-d918-4283-b138-c8ff8fb6e5e4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_multAt_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_minimalPrimes_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_divCycle_of_supp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_divCycle_one

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
variable {R : Type*} [CommRing R]
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (x : MRingOver F ι) (hx : x ≠ 0) [(Ideal.span {x}).IsPrime]
    (hrel : IsRelevant (Ideal.span {x})) (m : ℕ) :
    divCycle ⊥ (x ^ m) = Finsupp.single (Ideal.span {x}) m := by
  rcases m with _ | m
  · simp [inh_divCycle_one]
  have hm : (⊥ ⊔ Ideal.span {x ^ (m + 1)}).minimalPrimes = {Ideal.span {x}} := by
    rw [bot_sup_eq]
    apply inh_minimalPrimes_eq
    · rw [Ideal.span_singleton_le_span_singleton]; exact dvd_pow_self x (Nat.succ_ne_zero m)
    · intro q hq hle
      rw [Ideal.span_singleton_le_iff_mem] at hle ⊢
      exact hq.mem_of_pow_mem _ hle
  rw [inh_divCycle_of_supp ⊥ _ (Ideal.span {x}), bot_sup_eq, inh_multAt_pow x hx]
  ext W
  simp only [divSupp, hm, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.1
  · rintro rfl; exact ⟨rfl, hrel⟩
end ReciprocityTheory.ChartRestriction.G.AI.I1
