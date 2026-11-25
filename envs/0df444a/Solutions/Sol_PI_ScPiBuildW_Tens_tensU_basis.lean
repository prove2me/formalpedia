-- Prove2me | solution 1 for PI.ScPiBuildW.Tens.tensU_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:19:45.439246+00:00
-- url     : https://prove2.me/submissions/29176987-e94a-4391-9b46-c9fd05ddb644

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
import Theorems.Thm_PI_ScPiBuildW_Tens_tensU_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate
open Module
open PI PI.ScPiBuildW PI.ScPiBuildW.Tens
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Vl : ι → Type} [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)]
  [∀ i, FiniteDimensional ℂ (Vl i)]
namespace PI.ScPiBuildW.Tens
theorem _root_.solution (p : Idx Vl) : tensU (fun i => bas Vl i (p i)) = EuclideanSpace.single p 1 := by
  ext q
  rw [tensU_apply, PiLp.single_apply]
  by_cases hqp : q = p
  · subst hqp
    simp only [if_true]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [inner_self_eq_norm_sq_to_K, (bas Vl i).orthonormal.1 (q i)]
    simp
  · rw [if_neg hqp]
    obtain ⟨i, hi⟩ : ∃ i, q i ≠ p i := by
      by_contra hne
      push Not at hne
      exact hqp (funext hne)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    exact (bas Vl i).orthonormal.2 hi
end PI.ScPiBuildW.Tens
