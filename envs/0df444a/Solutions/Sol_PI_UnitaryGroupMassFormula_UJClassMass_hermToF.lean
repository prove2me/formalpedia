-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.hermToF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:06:22.522922+00:00
-- url     : https://prove2.me/submissions/0fbc22e2-b4b6-41ea-8d64-4f03a8a7b749

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
import Theorems.Thm_PIW_AdelClassFin_DictRing_algebraMap_injective
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_hcompl_le_primeCompl


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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable [StarRing E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (hst : ∀ a : F, star (algebraMap F E a) = algebraMap F E a)
    (v : HeightOneSpectrum (𝓞 F)) (X Y : Submodule (𝓞 E) V)
    (h : ∀ p : Ideal (𝓞 E), p.IsMaximal → p.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal →
      loc (K := E) p X = loc (K := E) p Y) : Floc v X ⊆ Floc v Y := by
  rintro x ⟨s, hs, hsx⟩
  classical
  let I : Ideal (𝓞 E) := Y.comap (LinearMap.toSpanSingleton (𝓞 E) V x)
  by_contra hno
  have hle : I.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal := by
    intro a ha
    by_contra hav
    exact hno ⟨a, hav, ha⟩
  obtain ⟨Q, hIQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal I hle
  have hQm : Q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 F) Q (by rw [hQc]; exact v.isMaximal)
  have hsQ : algebraMap (𝓞 F) (𝓞 E) s ∉ Q := fun hq => hs (by rw [← hQc]; exact hq)
  have hs' : algebraMap (𝓞 F) (𝓞 E) s ∈ hcompl (K := E) Q := by
    apply Submonoid.subset_closure
    refine ⟨hsQ, fun t ht => ?_⟩
    have e1 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) s) = algebraMap F E (algebraMap (𝓞 F) F s) := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    have : t = algebraMap (𝓞 F) (𝓞 E) s := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      rw [ht, e1, hst]
    rw [this]
    exact hsQ
  have hxX : x ∈ loc (K := E) Q X := ⟨_, hs', hsx⟩
  rw [h Q hQm hQc] at hxX
  obtain ⟨t, ht, htx⟩ := hxX
  haveI := hQm.isPrime
  exact (hcompl_le_primeCompl Q ht) (hIQ htx)
end PI.UnitaryGroupMassFormula.UJClassMass
