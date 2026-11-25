-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.interLocF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:27:32.750969+00:00
-- url     : https://prove2.me/submissions/6c7ccedc-b621-4ca6-9b11-62b9bff0dc79

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSSkeleton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjF
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_interLocStd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {V : Type}
  [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution [FiniteDimensional E V] (N : Submodule (𝓞 E) V) (hN : Submodule.IsLattice E N) (x : V)
    (hx : ∀ v : HeightOneSpectrum (𝓞 F), x ∈ Floc v N) : x ∈ N := by
  apply interLocStd N hN x
  intro p hp
  have hne : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField E)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hcb : p.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem ha0 ha (Algebra.IsIntegral.isIntegral (R := 𝓞 F) a)
  haveI := hp.isPrime
  let v : HeightOneSpectrum (𝓞 F) := ⟨p.comap (algebraMap (𝓞 F) (𝓞 E)), Ideal.comap_isPrime _ _, hcb⟩
  obtain ⟨s, hs, hsx⟩ := hx v
  exact ⟨algebraMap (𝓞 F) (𝓞 E) s, hs, hsx⟩
end PI.UnitaryGroupMassFormula.UJClassMass
