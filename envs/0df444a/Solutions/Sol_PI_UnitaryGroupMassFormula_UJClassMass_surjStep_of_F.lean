-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.surjStep_of_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:54:18.508005+00:00
-- url     : https://prove2.me/submissions/4e70027f-c790-4ae9-a43d-d5cc0c26a433

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSSkeleton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjF
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_mem_Floc_self
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_flocEq
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_finF
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_interLocF
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_cofinStep


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
theorem _root_.solution (hP : PatchF) (hS : SemiApprox) (hO : LSOne) : SurjStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hsymm hnd hL hsig N hN
  classical
  obtain ⟨D, hD0, hDL, hDN⟩ := cofinStep E V L0 N hL hN.1
  set T := (finF (F := F) D hD0).toFinset with hT
  have hTm : ∀ v, v ∉ T → ((D : 𝓞 F)) ∉ v.asIdeal := by
    intro v hv hDv
    exact hv ((Set.Finite.mem_toFinset _).2 hDv)
  obtain ⟨γ, hγ⟩ := hS F E σ V h M b L0 hσ hθ hsymm hnd hL N hN T
  have hsat : ∀ y : Fin M → E, PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) y ∈ latHat F E (crdOf b L0) →
      y ∈ crdOf b L0 := by
    intro y hy
    rw [← hO F E σ V h M b L0 hσ hθ hτ hsymm hnd hL hsig]
    show (finMat σ (gramOf h b) (1 : HA (AF F) σ (gramOf h b))⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) y) ∈
      latHat F E (crdOf b L0)
    rw [inv_one, finMat_one, Matrix.one_mulVec]
    exact hy
  obtain ⟨g, hg⟩ := hP F E σ V M (gramOf h b) b L0 hL hsat γ T
  refine ⟨g, ?_⟩
  rw [hg]
  ext x
  rw [Set.mem_setOf_eq]
  have hout : ∀ v, v ∉ T → Floc v L0 = Floc v N := fun v hv => flocEq v L0 N D (hTm v hv) hDL hDN
  constructor
  · rintro ⟨h1, h2⟩
    apply interLocF (F := F) N hN.1 x
    intro v
    by_cases hv : v ∈ T
    · rw [← hγ v hv]
      exact h1 v hv
    · rw [← hout v hv]
      exact h2 v hv
  · intro hx
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [hγ v hv]
      exact mem_Floc_self v N hx
    · rw [hout v hv]
      exact mem_Floc_self v N hx
end PI.UnitaryGroupMassFormula.UJClassMass
