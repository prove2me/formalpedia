-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.highest_weight_differences_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:35:56.547449+00:00
-- url     : https://prove2.me/submissions/2ce069a2-01a3-4870-95f5-690733ffa7c7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exists_nat_weight_sub_eq_of_highest_vector_in_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (hF : Formalism.REAL.KRel ε F) (S : Submodule ℂ M) [FiniteDimensional ℂ S]
    (hS : IsKStableSub ε F S) {μ : Fin n → ℝ} {v : M} (hv : v ∈ S) (hv0 : v ≠ 0)
    (hw : IsKHWVec ε F μ v) : ∀ a b, a < b → ε a = ε b → ∃ m : ℕ, μ a - μ b = m := by
  intro a b hab he
  obtain ⟨m, hm⟩ := exists_nat_weight_sub_eq_of_highest_vector_in_stable hF (ne_of_lt hab) he S (fun y hy => hS b a he.symm y hy) hv hv0
    (hw.1 a) (hw.1 b) (hw.2 a b hab he)
  refine ⟨m, ?_⟩
  apply Complex.ofReal_injective
  push_cast
  exact hm
end ReciprocityTheory.ChartRestriction.DS.HW
