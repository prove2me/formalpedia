-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.emb_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:56.839857+00:00
-- url     : https://prove2.me/submissions/660b7400-5578-4fe1-ad5c-46db5a9696f1

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
theorem _root_.solution (g : UJ (σ : E →+* E) J) : emb σ J g ∈ GamG σ J := by
  have : (show HR (AF F) σ J from emb σ J g).1 ∈ HFin (AF F) σ J := ⟨g.1, g.2, rfl⟩
  exact this
end PI.UnitaryGroupMassFormula.UJClassFin
