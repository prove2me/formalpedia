-- Prove2me | solution 1 for PI.ScRefExists.PPA.isInt_hG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:20:57.180852+00:00
-- url     : https://prove2.me/submissions/e91d00a2-1a63-432c-9137-d9e6e8519932

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_SpanSmulInto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_LocalAssemblyPrincipal

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
theorem _root_.solution {x y : Fin I.n → I.E} (hx : x ∈ I.L) (hy : y ∈ I.L) : IsInt I (hG I x y) := by
  obtain ⟨a, ha⟩ := (I.L_dual y).1 hy x hx
  exact ⟨a, ha⟩
end PI.ScRefExists.PPA
