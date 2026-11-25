-- Prove2me | solution 1 for PI.LocFramePrimWork.Dual_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:50:22.499306+00:00
-- url     : https://prove2.me/submissions/51bb9147-e4fe-4b33-a2fe-8430ab04b42f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DualFunctionalsExist

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
open NumberField IsDedekindDomain PI.LocFramePrim Module
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace PI.LocFramePrimWork
theorem _root_.solution {ι : Type} (g : ι → Fin n → E) (hg : LinearIndependent E g) (val : ι → E) :
    ∃ φ : (Fin n → E) →ₗ[E] E, ∀ i, φ (g i) = val i := by
  classical
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend ((Basis.span hg).constr E val)
  refine ⟨φ, fun i => ?_⟩
  have h1 : φ (g i) = ((Basis.span hg).constr E val) (Basis.span hg i) := by
    rw [← hφ, Basis.span_apply]
    rfl
  rw [h1, Basis.constr_basis]
end PI.LocFramePrimWork
