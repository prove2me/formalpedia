-- Prove2me | solution 1 for PI.VolSemiDirect.W.exists_proj_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:04.302858+00:00
-- url     : https://prove2.me/submissions/c3e2cfa6-4e9e-4c79-8740-9a761bcbafed

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_Closed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
namespace PI.VolSemiDirect.W
theorem _root_.solution (K : Submodule E (Fin n → E)) :
    ∃ P : Matrix (Fin n) (Fin n) E, (∀ x, P *ᵥ x ∈ K) ∧ ∀ x ∈ K, P *ᵥ x = x := by
  obtain ⟨K', hK⟩ := Submodule.exists_isCompl K
  refine ⟨LinearMap.toMatrix' (K.subtype ∘ₗ Submodule.linearProjOfIsCompl K K' hK), fun x => ?_, fun x hx => ?_⟩
  · rw [LinearMap.toMatrix'_mulVec]
    exact (Submodule.linearProjOfIsCompl K K' hK x).2
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.comp_apply]
    have := Submodule.linearProjOfIsCompl_apply_left hK ⟨x, hx⟩
    exact congrArg Subtype.val this
end PI.VolSemiDirect.W
