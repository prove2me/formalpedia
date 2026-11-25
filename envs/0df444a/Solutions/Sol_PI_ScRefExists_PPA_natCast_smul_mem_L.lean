-- Prove2me | solution 1 for PI.ScRefExists.PPA.natCast_smul_mem_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:20:50.289729+00:00
-- url     : https://prove2.me/submissions/a36e31b5-e303-4d97-a83c-d553b73a65d6

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
theorem _root_.solution (s : ℕ) {x : Fin I.n → I.E} (hx : x ∈ I.L) : (s : I.E) • x ∈ I.L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hx s
end PI.ScRefExists.PPA
