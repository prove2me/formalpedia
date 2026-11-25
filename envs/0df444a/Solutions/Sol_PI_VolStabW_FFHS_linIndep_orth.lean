-- Prove2me | solution 1 for PI.VolStabW.FFHS.linIndep_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:57:11.557887+00:00
-- url     : https://prove2.me/submissions/6f63f9a6-0206-4cd7-ab31-7ccbabbdbef0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFHS
import Theorems.Thm_PI_VolStabW_FFHS_IsSq_lin_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FFHS
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}
namespace PI.VolStabW.FFHS
theorem _root_.solution (hs : IsSq σ h) {n : ℕ} (f : Fin n → V)
    (h1 : ∀ i j, i ≠ j → h (f i) (f j) = 0) (h2 : ∀ i, h (f i) (f i) ≠ 0) :
    LinearIndependent K f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have := congrArg (hs.lin (f i)) hg
  rw [map_sum, map_zero, Finset.sum_eq_single i] at this
  · rw [map_smul, IsSq.lin_apply, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_right (h2 i)
  · intro j _ hji
    rw [map_smul, IsSq.lin_apply, h1 i j (Ne.symm hji), smul_zero]
  · simp
end PI.VolStabW.FFHS
