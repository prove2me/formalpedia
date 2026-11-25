-- Prove2me | solution 1 for PI.ScRefExists.PPA.QA_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:20:33.403933+00:00
-- url     : https://prove2.me/submissions/71c2af76-e0da-4288-a644-12646eab48dd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_NatCastSmulMemL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
namespace PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
private theorem mem_Ap_lemma (p : ℕ) (x : I.E) :
    x ∈ Ap I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E) :=
  Iff.rfl
end PI.ScRefExists.PPA
end
end

set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.PPA
theorem _root_.solution (p q : ℕ) {c x : I.E} (hc : c ∈ Ap I p) (hx : QA I p q x) : QA I p q (c * x) := by
  obtain ⟨s, hs, a, ha⟩ := hx
  obtain ⟨s0, hs0, a0, ha0⟩ := (mem_Ap_lemma I p c).mp hc
  refine ⟨s0 * s, Nat.Coprime.mul hs0 hs, a0 * a, ?_⟩
  push_cast
  linear_combination ((s : I.E) * x) * ha0 + (a0 : I.E) * ha
end PI.ScRefExists.PPA
