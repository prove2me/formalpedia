-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.finMat_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:28.655088+00:00
-- url     : https://prove2.me/submissions/bcdc19ac-f8e5-48b9-8b91-b8b768d06317

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
theorem _root_.solution (g : UJ (σ : E →+* E) J) :
    finMat σ J (emb σ J g) = ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (Af F)) := by
  ext i j
  change (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))
      ((1 : AF F) ⊗ₜ[F] ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) i j) =
    (1 : Af F) ⊗ₜ[F] ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) i j
  simp [Algebra.TensorProduct.map_tmul]
end PI.UnitaryGroupMassFormula.UJClassFin
