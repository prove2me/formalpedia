-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.map_mulVec_vinc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:34.109706+00:00
-- url     : https://prove2.me/submissions/d41f0be3-9d53-43b3-ac46-de20f404c195

import Definitions.Def_Formalism_PeriodIntegrals_UJClassFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development

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
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (A : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    (A.map (inclR (Af F))).mulVec (vinc (F := F) x) = vinc (F := F) (A.mulVec x) := by
  ext i
  simp only [vinc]
  rw [RingHom.map_mulVec]
  rfl
end PI.UnitaryGroupMassFormula.UJClassFin
