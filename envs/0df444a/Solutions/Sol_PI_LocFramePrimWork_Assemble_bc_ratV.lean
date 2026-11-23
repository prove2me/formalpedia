-- Prove2me | solution 1 for PI.LocFramePrimWork.Assemble_bc_ratV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:37.60299+00:00
-- url     : https://prove2.me/submissions/53d061ab-9a57-46f4-8fdf-782fcd99305c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_Assemble

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
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
namespace PI.LocFramePrimWork
theorem _root_.solution (ψ : (Fin n → E) →ₗ[E] E) (y : Fin n → E) :
    Assemble_bc v ψ (ratV (F := F) (Fv F v) y) = inclR (F := F) (Fv F v) (ψ y) := by
  conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ ψ y]
  simp only [Assemble_bc, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.coe_proj, Function.eval, ratV, smul_eq_mul, map_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end PI.LocFramePrimWork
