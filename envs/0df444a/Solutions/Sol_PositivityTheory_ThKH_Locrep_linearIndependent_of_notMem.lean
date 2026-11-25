-- Prove2me | solution 1 for PositivityTheory.ThKH.Locrep.linearIndependent_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:01:52.393978+00:00
-- url     : https://prove2.me/submissions/65c363b5-8d94-4e11-a0e9-23a7f6b2b9ad

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsSideBis
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_LinearIndependentOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Locrep
open Filter Topology
namespace PositivityTheory.ThKH.Locrep
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (u : ℕ → V) (T : ℕ → Set V)
    (h1 : ∀ m n, m < n → u m ∈ T n) (h2 : ∀ n, u n ∉ Submodule.span ℂ (T n)) : LinearIndependent ℂ u := by
  classical
  rw [linearIndependent_iff']
  intro s g
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hs ih =>
    intro hsum
    have ha : a ∉ s := fun h => lt_irrefl _ (hs a h)
    rw [Finset.sum_insert ha] at hsum
    have h0 : g a = 0 := by
      by_contra hne
      refine h2 a ((Submodule.smul_mem_iff _ hne).1 ?_)
      rw [eq_neg_of_add_eq_zero_left hsum]
      exact neg_mem (Submodule.sum_mem _ fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span (h1 i a (hs i hi))))
    rw [h0, zero_smul, zero_add] at hsum
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact h0
    · exact ih hsum i hi
end PositivityTheory.ThKH.Locrep
