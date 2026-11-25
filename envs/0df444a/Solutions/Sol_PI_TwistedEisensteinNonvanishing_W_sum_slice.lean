-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.sum_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:53.869177+00:00
-- url     : https://prove2.me/submissions/178f6c92-481b-4b55-85f2-8c87b6ad9b55

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_SumSliceEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE Function
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution (k : ι) (S : ι → Finset E) (u0 : E) (F : (ι → E) → K) :
    ∑ t ∈ Fintype.piFinset S, F t =
      ∑ t ∈ Fintype.piFinset (update S k {u0}), ∑ u ∈ S k, F (update t k u) := by
  rw [← Finset.sum_product' (f := fun t u => F (update t k u))]
  refine Finset.sum_nbij' (fun t => (update t k u0, t k)) (fun p => update p.1 k p.2) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_product] at ht ⊢
    refine ⟨fun i => ?_, ht k⟩
    by_cases hi : i = k
    · subst hi; simp
    · simp [Function.update_of_ne hi, ht i]
  · intro p hp
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_product] at hp ⊢
    intro i
    by_cases hi : i = k
    · subst hi; simpa using hp.2
    · simpa [Function.update_of_ne hi] using hp.1 i
  · intro t _
    simp
  · intro p hp
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_product] at hp
    have h1 : p.1 k = u0 := by simpa using hp.1 k
    refine Prod.ext ?_ ?_
    · show update (update p.1 k p.2) k u0 = p.1
      rw [Function.update_idem, ← h1, Function.update_eq_self]
    · simp
  · intro t _
    simp
end PI.TwistedEisensteinNonvanishing.W
