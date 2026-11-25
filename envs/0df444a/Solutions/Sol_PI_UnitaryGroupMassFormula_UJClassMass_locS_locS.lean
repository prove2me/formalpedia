-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.locS_locS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:27:09.36258+00:00
-- url     : https://prove2.me/submissions/a5789a31-90f5-4582-9e88-2a99a2721b5a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_GmapLeLocS
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_le_locS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (S : Submonoid (𝓞 E)) (X : Submodule (𝓞 E) V) : locS S (locS S X) = locS S X := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, t, ht, hx⟩ := hx
    exact (mem_locS_iff' S X x).2 ⟨t * s, S.mul_mem ht hs, by rwa [mul_smul]⟩
  · exact le_locS S _
end PI.UnitaryGroupMassFormula.UJClassMass
