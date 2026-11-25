-- Prove2me | solution 1 for PIW.AdelClassFin.kset_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:20:38.479747+00:00
-- url     : https://prove2.me/submissions/85300d73-141b-45e2-9fb3-057c387d1fde

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_KsetMulVecMem

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
namespace PIW.AdelClassFin
theorem _root_.solution (I : AutInst) {k t : I.Gf} (hk : k ∈ I.Kset) (ht : t ∈ I.Kset) : k * t ∈ I.Kset := by
  show ((k * t : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [Subgroup.coe_mul]
  exact Subgroup.mul_mem _ hk ht
end PIW.AdelClassFin
