-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.gLoc_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:58.753074+00:00
-- url     : https://prove2.me/submissions/e8035b03-b48d-441f-bef1-74091e39e4f8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PsiInclR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (g : HA (AF F) σ J) (v : HeightOneSpectrum (𝓞 F)) :
    ((gLoc σ J g v : GL (Fin M) (E ⊗[F] Fv F v)) : Matrix (Fin M) (Fin M) (E ⊗[F] Fv F v)) =
      (finMat σ J g).map (Psi v) := rfl
end PI.UnitaryGroupMassFormula.UJClassMass
