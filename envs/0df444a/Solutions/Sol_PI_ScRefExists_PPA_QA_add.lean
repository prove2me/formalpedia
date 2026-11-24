-- Prove2me | solution 1 for PI.ScRefExists.PPA.QA_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:01:22.445707+00:00
-- url     : https://prove2.me/submissions/f72e13a1-86d2-4c04-8fcf-1baec7d5d14d

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
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.PPA
theorem _root_.solution (p q : ℕ) {x y : I.E} (hx : QA I p q x) (hy : QA I p q y) : QA I p q (x + y) := by
  obtain ⟨s, hs, a, ha⟩ := hx
  obtain ⟨t, ht, b, hb⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul hs ht, (t : 𝓞 I.E) * a + (s : 𝓞 I.E) * b, ?_⟩
  push_cast at ha hb ⊢
  linear_combination (t : I.E) * ha + (s : I.E) * hb
end PI.ScRefExists.PPA
