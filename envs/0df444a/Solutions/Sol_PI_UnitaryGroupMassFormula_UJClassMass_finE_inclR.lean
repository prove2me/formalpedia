-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.finE_inclR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:21.196999+00:00
-- url     : https://prove2.me/submissions/17bbafc4-5ee9-4b52-89c7-8bf0471381f5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (x : E) : finE F E (inclR (AF F) x) = inclR (Af F) x := by
  show Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl
end PI.UnitaryGroupMassFormula.UJClassMass
