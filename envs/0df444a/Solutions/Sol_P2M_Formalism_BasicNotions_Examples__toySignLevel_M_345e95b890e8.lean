-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__toySignLevel_M_345e95b890e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:22.368742+00:00
-- url     : https://prove2.me/submissions/899e6507-42e8-4350-95d9-31e71f4b24ea

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GPlacesExampleNatAct
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__emptyPlaces_natAct_93c637f18902
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
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
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Formalism.BasicNotions NumberField IsDedekindDomain
open Formalism.MainNotions.G
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (p : ℕ) : (toySignLevel p).M = ⊥ := by
  rw [eq_bot_iff]
  intro F hF
  rw [Submodule.mem_bot]
  funext L
  have h := hF
  simp only [Level.M, Level.funMod, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at h
  have h1 := h.2 (show (toySignLevel p).Γ from (-1 : ℤˣ)) L
  have hs : (toySignLevel p).smul (show (toySignLevel p).Γ from (-1 : ℤˣ)) L = L := Subsingleton.elim _ _
  simp only [LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    hs] at h1
  have hc : ((toySignLevel p).χ (show (toySignLevel p).Γ from (-1 : ℤˣ)) : ℤ_[3]) = -1 := by
    show ((Units.map (Int.castRingHom ℤ_[3]).toMonoidHom (-1 : ℤˣ) : ℤ_[3]ˣ) : ℤ_[3]) = -1
    simp
  rw [hc] at h1
  have e : (((toySignLevel p).actX (show (toySignLevel p).Γ from (-1 : ℤˣ))).restrictScalars
      ℤ_[3]) (F L) = F L := by
    show (emptyPlaces p).natAct _ (F L) = F L
    rw [emptyPlaces_natAct]
    rfl
  rw [e, neg_one_smul, sub_neg_eq_add] at h1
  have h2 : (2 : ℚ_[3]) • F L = 0 := by rw [two_smul]; exact h1
  simpa using (smul_eq_zero.mp h2).resolve_left two_ne_zero
end Formalism.BasicNotions.Examples₂
