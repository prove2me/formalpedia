-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.mem_imgLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:59.209803+00:00
-- url     : https://prove2.me/submissions/77e3e995-a5f5-4c7a-8261-347dd3b7650a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution {m : Type} {δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)} {Λ : AddSubgroup (m → ℂ)} {z : m → ℂ} :
    z ∈ UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ ↔ δ.symm z ∈ Λ := by
  simp only [UnitDetRootDefs.imgLat, AddSubgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩; simpa using hw
  · intro h; exact ⟨δ.symm z, h, by simp⟩
end PI.UnitaryGroupMassFormula.UnitDetRoot
