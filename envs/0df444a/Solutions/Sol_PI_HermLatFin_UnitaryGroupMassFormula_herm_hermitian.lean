-- Prove2me | solution 1 for PI.HermLatFin.UnitaryGroupMassFormula.herm_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:14.84539+00:00
-- url     : https://prove2.me/submissions/73395593-d5fb-4fc5-a991-e9c4dbab3493

import Definitions.Def_Formalism_PeriodIntegrals_HermLatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianLatticeFiniteness_HformTracePos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexOrder
noncomputable section
open PI PI.HermLatFin PI.HermLatFin.UnitaryGroupMassFormula
variable {E : Type} [Field E] [NumberField E]
namespace PI.HermLatFin.UnitaryGroupMassFormula
theorem _root_.solution {n : ℕ} (σ : E →+* E)
    (hσ : ∀ τ : E →+* ℂ, ∀ a : E, τ (σ a) = starRingEnd ℂ (τ a))
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ τ : E →+* ℂ, (J.map τ).PosDef) (i j : Fin n) :
    σ (J i j) = J j i := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hσ]
  have h := congrFun (congrFun (hJ τ).isHermitian j) i
  rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply] at h
  rw [starRingEnd_apply]
  exact h
end PI.HermLatFin.UnitaryGroupMassFormula
