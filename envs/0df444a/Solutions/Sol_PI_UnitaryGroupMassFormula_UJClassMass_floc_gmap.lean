-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.floc_gmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:45:24.654012+00:00
-- url     : https://prove2.me/submissions/88f9f865-d2e4-4932-96e2-55e94bf74a28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PPatchF
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_equiv_smul_O
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_mem_gmap_iff
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



set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (v : HeightOneSpectrum (𝓞 F)) (u : V ≃ₗ[E] V) (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ Floc v (gmap u L) ↔ u.symm x ∈ Floc v L := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    rw [mem_gmap_iff] at hsx
    obtain ⟨y, hy, hyx⟩ := hsx
    refine ⟨s, hs, ?_⟩
    rw [← equiv_smul_O u.symm, ← hyx]
    simpa using hy
  · rintro ⟨s, hs, hsx⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_gmap_iff]
    refine ⟨_, hsx, ?_⟩
    rw [equiv_smul_O u, LinearEquiv.apply_symm_apply]
end PI.UnitaryGroupMassFormula.UJClassMass
