-- Prove2me | solution 1 for ResidualGaloisRep.map_localFlatClasses_le_localFlatClassesAd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/0eb09324-76f8-591e-974a-616650631d77

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_map_localFlatClasses_le_localFlatClassesAd

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem solution
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (φ : Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero ⟶
      Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))
    (hφ : ∀ x : LinearMap.ker (LinearMap.trace k ρbar.V), φ.hom x = (x : Module.End k ρbar.V)) :
    (ρbar.localFlatClasses p).map
        (groupCohomology.map (A := Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)
          (MonoidHom.id (primeLocalGaloisGroup (pPrime p))) φ 1).hom ≤
      ρbar.localFlatClassesAd p := by
  rw [ResidualGaloisRep.localFlatClasses, Submodule.map_span_le]
  rintro _ ⟨c0, hc0, rfl⟩
  have hval : ∀ σ, (mapCocycles₁ (MonoidHom.id (primeLocalGaloisGroup (pPrime p))) φ c0) σ =
      ((c0 σ : LinearMap.ker (LinearMap.trace k ρbar.V)) : Module.End k ρbar.V) :=
    fun σ => hφ (c0 σ)
  have key : ρbar.dualLiftModuleActAd p
      (mapCocycles₁ (MonoidHom.id (primeLocalGaloisGroup (pPrime p))) φ c0) =
      ρbar.dualLiftModuleAct p c0 := by
    funext σ x
    simp only [ResidualGaloisRep.dualLiftModuleAct, ResidualGaloisRep.dualLiftModuleActAd, hval]
  refine Submodule.subset_span ⟨mapCocycles₁ (MonoidHom.id _) φ c0, ?_, ?_⟩
  · unfold ResidualGaloisRep.IsLocallyFlatCocycleAd
    rw [key]
    exact hc0
  · erw [H1π_comp_map_apply]

end S_ResidualGaloisRep_map_localFlatClasses_le_localFlatClassesAd
end P2MW
export P2MW.S_ResidualGaloisRep_map_localFlatClasses_le_localFlatClassesAd (solution)
