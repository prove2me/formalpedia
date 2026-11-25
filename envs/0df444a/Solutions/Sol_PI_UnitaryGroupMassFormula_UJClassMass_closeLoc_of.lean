-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.closeLoc_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:10:39.801818+00:00
-- url     : https://prove2.me/submissions/19ba7058-2d20-41c0-ad81-9bc6ac6cf16e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermSk
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermCL
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (hT : TensLoc) (hL : LatClose) : CloseLoc := by
  intro F E _ _ _ _ _ σ V _ _ _ _ _ M J b L0 hσσ hH hdet hL0 g hg
  obtain ⟨δ, hδ, hTδ⟩ := hT F E
  obtain ⟨D, hD, hDcl⟩ := hL F E σ V M J b L0 hσσ hH hdet hL0 g hg
  refine ⟨δ * D, mul_ne_zero hδ hD, fun D' hD' γ hγ t hcong => ?_⟩
  obtain ⟨k, rfl⟩ := hD'
  refine hDcl (D * k) (dvd_mul_right D k) γ hγ (Sw F E t) ?_ ?_
  · rintro r ⟨a, -, rfl⟩
    change σ (algebraMap F E (a : F)) = algebraMap F E (a : F)
    exact σ.commutes _
  · intro i j
    obtain ⟨s, hs, he⟩ := hcong i j
    obtain ⟨r, hr, y, hry⟩ := hTδ t (((g : Matrix (Fin M) (Fin M) E) i j) - (γ : Matrix (Fin M) (Fin M) E) i j)
      (δ * D * k) ⟨s, hs, by rw [map_sub]; exact he⟩
    refine ⟨r, hr, y, ?_⟩
    have hδF : (δ : F) ≠ 0 := by simpa using hδ
    have hδE : algebraMap F E (δ : F) ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).2 hδF
    apply mul_left_cancel₀ hδE
    have e1 : ((δ * D * k : 𝓞 F) : F) = (δ : F) * ((D * k : 𝓞 F) : F) := by push_cast; ring
    rw [e1, map_mul] at hry
    linear_combination hry
end PI.UnitaryGroupMassFormula.UJClassMass
