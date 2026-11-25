-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.semiApprox_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:37:10.659417+00:00
-- url     : https://prove2.me/submissions/e6016065-968c-4a1c-8577-401a04f8c607

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_primesOver_finite
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_hermToF

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
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (hH : HermApprox) : SemiApprox := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hsymm hnd hL N hN T
  classical
  set P := (primesOver_finite (E := E) T).toFinset with hP
  obtain ⟨γ, hγ⟩ := hH F E σ V h M b L0 hσ hθ hsymm hnd hL N hN P
    (fun p hp => ((Set.Finite.mem_toFinset _).1 hp).1)
  refine ⟨γ, fun v hv => ?_⟩
  have hst : ∀ a : F, star (algebraMap F E a) = algebraMap F E a := fun a => by
    rw [← hσ, AlgHom.commutes]
  have hpv : ∀ p : Ideal (𝓞 E), p.IsMaximal → p.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal →
      loc (K := E) p (gmap (linOf b (γ : GL (Fin M) E)) L0) = loc (K := E) p N :=
    fun p hp hc => hγ p ((Set.Finite.mem_toFinset _).2 ⟨hp, v, hv, hc⟩)
  exact Set.Subset.antisymm (hermToF hst v _ _ hpv) (hermToF hst v _ _ (fun p hp hc => (hpv p hp hc).symm))
end PI.UnitaryGroupMassFormula.UJClassMass
