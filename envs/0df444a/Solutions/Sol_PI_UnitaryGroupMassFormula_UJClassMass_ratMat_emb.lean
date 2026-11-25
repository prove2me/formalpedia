-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.ratMat_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:41.340228+00:00
-- url     : https://prove2.me/submissions/04b525ab-5002-4c45-a493-86349a5092c0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_bc_injective
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_emb_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (U : UJ (σ : E →+* E) J) :
    ratMat σ J ⟨PI.UnitaryGroupMassFormula.UJClassFin.emb σ J U, PI.UnitaryGroupMassFormula.UJClassFin.emb_mem σ J U⟩ = U :=
  bc_injective (ratMat_spec σ J _).2
end PI.UnitaryGroupMassFormula.UJClassMass
