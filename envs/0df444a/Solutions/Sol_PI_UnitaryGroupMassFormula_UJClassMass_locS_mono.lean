-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.locS_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:55:50.022229+00:00
-- url     : https://prove2.me/submissions/f7bed624-b024-4831-81f1-d6f8bf5adb6c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_GmapLeLocS
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
theorem _root_.solution (S : Submonoid (𝓞 E)) {X Y : Submodule (𝓞 E) V} (h : X ≤ Y) : locS S X ≤ locS S Y := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := hx
  exact (mem_locS_iff' S Y x).2 ⟨s, hs, h hx⟩
end PI.UnitaryGroupMassFormula.UJClassMass
