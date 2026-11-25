-- Prove2me | solution 1 for PI.TensCpctDenWork.coordL_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:29:40.548435+00:00
-- url     : https://prove2.me/submissions/6f4ad5c7-9c2e-471c-af5d-6f1f9614e172

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactTensorDensity_TensCpctDenOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.TensCpctDenWork
open NumberField IsDedekindDomain TensorProduct
variable {F E R : Type} [Field F] [CommRing E] [Algebra F E] [CommRing R] [Algebra F R]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace PI.TensCpctDenWork
theorem _root_.solution (φ : E →ₗ[F] F) (e : E) (x : R) : coordL φ (e ⊗ₜ[F] x) = φ e • x :=
  coordR_tmul φ e x
end PI.TensCpctDenWork
