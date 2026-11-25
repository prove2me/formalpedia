-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_UJClassFin_nsmul_tmul__c42d1c934366
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:16.212927+00:00
-- url     : https://prove2.me/submissions/811c85e2-d49f-400e-a744-d592d9153b2e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (m n : ℕ) (a : Af F) (e : E) :
    (m * n) • (a ⊗ₜ[F] e) = ((m : Af F) * a) ⊗ₜ[F] ((n : E) * e) := by
  rw [← Nat.cast_smul_eq_nsmul F, Nat.cast_mul, mul_smul, ← TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']
  congr 1
  · rw [Algebra.smul_def, map_natCast]
  · rw [Algebra.smul_def, map_natCast]
end PI.UnitaryGroupMassFormula.UJClassFin
