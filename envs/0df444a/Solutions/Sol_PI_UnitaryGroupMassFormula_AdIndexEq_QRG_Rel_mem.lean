-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.QRG.Rel_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:43.392527+00:00
-- url     : https://prove2.me/submissions/1eabf0c4-6646-4506-b9b6-f72e48543a49

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.QRG
open Matrix Formalism.UG
variable {K : Type} [Field K] {n : ℕ}
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
namespace PI.UnitaryGroupMassFormula.AdIndexEq.QRG
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (a : Fin n → K) (α : K) (hα : σ α * α = 1)
    (ha : H σ J a a ≠ 0) : Rel σ J hσ hJ a α hα ha ∈ S σ J := by exact Subgroup.subset_closure ⟨Pm σ J a, α, Pm_idem σ J a ha, hα, rfl⟩
end PI.UnitaryGroupMassFormula.AdIndexEq.QRG
