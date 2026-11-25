-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.locGmapStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:04:10.787925+00:00
-- url     : https://prove2.me/submissions/33ae57e7-22a1-4a48-85ab-b0307dfca21b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjSk
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_mem_loc_iff
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_mem_gmap_iff
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_equiv_smul_O

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution : LocGmapStep := by
  intro E _ _ _ V _ _ _ _ u p L
  ext x
  rw [mem_loc_iff, mem_gmap_iff]
  constructor
  · rintro ⟨s, hs, hsx⟩
    rw [mem_gmap_iff] at hsx
    obtain ⟨y, hy, hyx⟩ := hsx
    refine ⟨u.symm x, ?_, u.apply_symm_apply x⟩
    rw [mem_loc_iff]
    refine ⟨s, hs, ?_⟩
    have h3 : s • u.symm x = y := by
      apply u.injective
      rw [equiv_smul_O, u.apply_symm_apply, hyx]
    rw [h3]
    exact hy
  · rintro ⟨y, hy, rfl⟩
    rw [mem_loc_iff] at hy
    obtain ⟨s, hs, hsy⟩ := hy
    refine ⟨s, hs, ?_⟩
    rw [mem_gmap_iff]
    exact ⟨s • y, hsy, equiv_smul_O u s y⟩
end PI.UnitaryGroupMassFormula.UJClassMass
