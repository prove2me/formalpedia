-- Prove2me | solution 1 for PIW.AdelClassFin.DictGen.natSmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:50:12.114034+00:00
-- url     : https://prove2.me/submissions/d06ec4a0-25d1-403a-8eb2-35c240ac4bdc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen

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
theorem _root_.solution (k : ℕ) {w : Fin I.n → I.E ⊗[I.F] Af I.F} (hw : w ∈ I.Lf) :
    (k : I.E ⊗[I.F] Af I.F) • w ∈ I.Lf := by
  first
    | rw [Nat.cast_smul_eq_nsmul (I.E ⊗[I.F] Af I.F)]
      exact nsmul_mem hw k
    | rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem hw k
    | exact I.Lf.smul_mem (k : IntAf I.F I.E) hw
end PIW.AdelClassFin.DictGen
