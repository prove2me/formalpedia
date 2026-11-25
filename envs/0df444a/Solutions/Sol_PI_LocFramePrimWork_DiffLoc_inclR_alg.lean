-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_inclR_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:49:56.617739+00:00
-- url     : https://prove2.me/submissions/adcc4b61-93aa-416e-b585-c1b6e84c51ab

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocFramePrimWork
theorem _root_.solution (x : F) :
    inclR (F := F) (Fv F v) (algebraMap F E x) = sc (E := E) v (algebraMap F (Fv F v) x) := by
  show (1 : Fv F v) ⊗ₜ[F] (algebraMap F E x) = (algebraMap F (Fv F v) x) ⊗ₜ[F] (1 : E)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  exact (TensorProduct.smul_tmul x (1 : Fv F v) (1 : E)).symm
end PI.LocFramePrimWork
