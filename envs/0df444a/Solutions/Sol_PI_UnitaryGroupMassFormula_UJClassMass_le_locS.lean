-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.le_locS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:54:22.307191+00:00
-- url     : https://prove2.me/submissions/4be7d2c2-b0e5-4c4f-a763-55da9d22c761

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_GmapLeLocS
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
section Glob
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V] {M : ℕ}
private theorem mem_locS_iff' (S : Submonoid (𝓞 E)) (X : Submodule (𝓞 E) V) (x : V) :
    x ∈ locS S X ↔ ∃ s ∈ S, s • x ∈ X := Iff.rfl
end Glob
end PI.UnitaryGroupMassFormula.UJClassMass
end
end

set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V] {M : ℕ}
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (S : Submonoid (𝓞 E)) (X : Submodule (𝓞 E) V) : X ≤ locS S X := fun x hx => (mem_locS_iff' S X x).2 ⟨1, S.one_mem, by simpa using hx⟩
end PI.UnitaryGroupMassFormula.UJClassMass
