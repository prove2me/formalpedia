-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.exists_finset_iInf_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:54.957141+00:00
-- url     : https://prove2.me/submissions/1a3e5400-3b96-401b-b1a4-fc4da463f12e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open Module
variable {V k : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field k] [Algebra V k] [FaithfulSMul V k]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {M : Type} [AddCommGroup M] [Module k M] [FiniteDimensional k M] {O : Type}
    (K : O → Submodule k M) : ∃ F : Finset O, ∀ b, (⨅ a ∈ F, K a) ≤ K b := by
  classical
  obtain ⟨N, ⟨F, rfl⟩, hmin⟩ := (wellFounded_lt (α := Submodule k M)).has_min
    {N | ∃ F : Finset O, N = ⨅ a ∈ F, K a} ⟨⊤, ∅, by simp⟩
  refine ⟨F, fun b => ?_⟩
  have hle : (⨅ a ∈ insert b F, K a) ≤ ⨅ a ∈ F, K a := by
    rw [Finset.iInf_insert]
    exact inf_le_right
  have heq : (⨅ a ∈ insert b F, K a) = ⨅ a ∈ F, K a := by
    by_contra hne
    exact hmin _ ⟨insert b F, rfl⟩ (lt_of_le_of_ne hle hne)
  rw [← heq, Finset.iInf_insert]
  exact inf_le_left
end ReciprocityTheory.ChartRestriction.G.Chart
