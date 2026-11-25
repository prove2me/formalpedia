-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.vol_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:46:19.943693+00:00
-- url     : https://prove2.me/submissions/14b2776f-e049-406c-880e-add24ccd7379

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobVol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
variable (F : IntermediateField ℚ ℂ) {m : Type} [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution {Λ Λ' : AddSubgroup (m → ℂ)} (c : ℂ) (h : ∀ x ∈ Λ, c • x ∈ Λ') :
    Submodule.span (𝓞 F) {c ^ Fintype.card m} * vol F Λ ≤ vol F Λ' := by
  unfold vol volSet
  rw [Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, _, ⟨v, hv, rfl⟩, rfl⟩
  obtain rfl := Set.mem_singleton_iff.mp hx
  apply Submodule.subset_span
  refine ⟨fun j => c • v j, fun j => h _ (hv j), ?_⟩
  rw [show (Matrix.of fun j => c • v j) = c • Matrix.of v from by ext i j; rfl, Matrix.det_smul]
end PI.UnitaryGroupMassFormula.UnitDetRoot
