-- Prove2me | solution 1 for PI.VolStabW.DeterminantAdmissible.finprod_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:56:02.31766+00:00
-- url     : https://prove2.me/submissions/0ae66bb3-e778-412b-ab7a-b92389f53f15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DeterminantAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabW.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabW
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {a M : ℕ}
variable {b}
namespace PI.VolStabW.DeterminantAdmissible
theorem _root_.solution {α : Type} (P : α → Prop) [DecidablePred P] [Decidable (∀ v, P v)] (h : ∀ᶠ v in cofinite, P v) :
    ∏ᶠ v, (if P v then (1 : ℂ) else 0) = if ∀ v, P v then 1 else 0 := by
  by_cases hall : ∀ v, P v
  · rw [if_pos hall]
    exact finprod_eq_one_of_forall_eq_one fun v => if_pos (hall v)
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨v0, hv0⟩ := hall
    refine finprod_eq_zero _ v0 (if_neg hv0) ?_
    refine (eventually_cofinite.1 h).subset fun v hv => ?_
    intro hP
    exact hv (if_pos hP)
end PI.VolStabW.DeterminantAdmissible
