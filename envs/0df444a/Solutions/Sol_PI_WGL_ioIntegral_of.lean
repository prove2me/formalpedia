-- Prove2me | solution 1 for PI.WGL.ioIntegral_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:00.864142+00:00
-- url     : https://prove2.me/submissions/f6ccfebd-4f72-4f11-853f-d3baab0e4b4f

import Definitions.Def_Formalism_PeriodIntegrals_GTLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_Assembly
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL
theorem _root_.solution (hZ : CapelliZ) (hL : LiftMod) (hV : ZScalarVanish) : IoIntegral := by
  intro n N h lam sg hI io0 hE hx hW s hs
  obtain ⟨Z, hZi, hZa⟩ := hZ n N h lam sg hI
  obtain ⟨m, hm, hd⟩ := hL n N h lam sg hI io0 hE hx hW s hs
  obtain ⟨f', hf', hZf⟩ := hZi m hm
  refine ⟨f', hf', ?_⟩
  have hsC : MvPolynomial.map (Int.castRingHom ℂ) s ∈ nablaSq ℂ n sg :=
    Formalism.GradedWeylDivisibility.dualWeylMap ℤ ℂ (Int.castRingHom ℂ) n n sg.natW s hs
  have hO : OtherPart h lam sg ≤ LinearMap.ker Z := by
    unfold OtherPart
    refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun hne => iSup_le fun hw =>
      iSup_le fun φ => iSup_le fun hφ => ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [LinearMap.mem_ker, hZa mu hmu φ hφ t ht, hV n N h lam sg mu hI hmu hne hw, Int.cast_zero, zero_smul]
  have h0 := hO hd
  rw [LinearMap.mem_ker, map_sub, hZf, hZa sg hI io0 hE _ hsC] at h0
  have hz : zScalar h lam sg sg = cBr h lam sg := rfl
  rw [hz] at h0
  rw [map_smul]
  exact (sub_eq_zero.mp h0).symm
end PI.WGL
