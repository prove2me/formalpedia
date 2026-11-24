-- Prove2me | solution 1 for PIW.AdelClassFin.DictGen.iv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:54:45.364801+00:00
-- url     : https://prove2.me/submissions/5999a8ac-26d0-4363-8443-a3f90371fd4f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
import Theorems.Thm_PIW_AdelClassFin_DictGen_lf_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
open PIW.AdelClassFin.DictGen
variable (I : AutInst)
namespace PIW.AdelClassFin.DictGen
theorem _root_.solution {l : Fin I.n → I.E} (hl : l ∈ I.L) : iv I l ∈ I.Lf := by
  rw [lf_eq]
  exact Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
end PIW.AdelClassFin.DictGen
