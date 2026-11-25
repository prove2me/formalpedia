-- Prove2me | solution 1 for PI.WAU.Cpt.intC_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:06.681296+00:00
-- url     : https://prove2.me/submissions/1ddff08a-153a-40f9-aa0f-8e3d232e69a8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_LamAfLeOhatL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_MulVecMemLf
import Theorems.Thm_PI_WAU_intC_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
open PI.WAU.Cpt
variable (I : AutInst)
namespace PI.WAU.Cpt
theorem _root_.solution (D1 : ℕ) (h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F))) (j : Fin I.n) :
    ∀ i, IntC (bs I) ((Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F) i) := by
  intro i
  by_cases hij : i = j
  · subst hij; rw [Pi.single_eq_same]; exact h1
  · rw [Pi.single_eq_of_ne hij]; exact intC_zero
end PI.WAU.Cpt
