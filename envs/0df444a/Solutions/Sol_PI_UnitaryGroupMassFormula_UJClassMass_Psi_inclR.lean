-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.Psi_inclR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:15:49.239797+00:00
-- url     : https://prove2.me/submissions/5b855636-8ba8-44d3-82ca-0360222857d8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PsiInclR
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_Psi_tmul


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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    Psi v (inclR (F := F) (Af F) e) = PI.UnitaryApproxDefs.inclE (F := F) (Fv F v) e := by
  show Psi v ((1 : Af F) ⊗ₜ[F] e) = e ⊗ₜ[F] (1 : Fv F v)
  rw [Psi_tmul]; rfl
end PI.UnitaryGroupMassFormula.UJClassMass
