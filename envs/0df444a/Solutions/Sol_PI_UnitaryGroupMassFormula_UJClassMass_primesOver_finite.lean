-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.primesOver_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:38.800291+00:00
-- url     : https://prove2.me/submissions/12e16830-f255-47d6-b827-7fe9f66251de

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_finMaxElt
import Theorems.Thm_PIW_AdelClassFin_DictRing_algebraMap_injective


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
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (T : Finset (HeightOneSpectrum (𝓞 F))) :
    {p : Ideal (𝓞 E) | p.IsMaximal ∧ ∃ v ∈ T, p.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal}.Finite := by
  classical
  have ha : ∀ v : HeightOneSpectrum (𝓞 F), ∃ a : 𝓞 F, a ∈ v.asIdeal ∧ a ≠ 0 :=
    fun v => Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  choose a haM ha0 using ha
  have hne0 : ∀ x : 𝓞 F, x ≠ 0 → algebraMap (𝓞 F) (𝓞 E) x ≠ 0 := by
    intro x hx h0
    have h1 : algebraMap (𝓞 F) E x = 0 := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, h0, map_zero]
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, map_eq_zero_iff _ (algebraMap F E).injective] at h1
    exact hx (FaithfulSMul.algebraMap_injective (𝓞 F) F (by rw [h1, map_zero]))
  apply (T.finite_toSet.biUnion (fun v _ => finMaxElt (algebraMap (𝓞 F) (𝓞 E) (a v))
    (hne0 (a v) (ha0 v)))).subset
  rintro p ⟨hp, v, hv, hc⟩
  refine Set.mem_biUnion (x := v) hv ⟨hp, ?_⟩
  have : a v ∈ p.comap (algebraMap (𝓞 F) (𝓞 E)) := by rw [hc]; exact haM v
  exact this
end PI.UnitaryGroupMassFormula.UJClassMass
