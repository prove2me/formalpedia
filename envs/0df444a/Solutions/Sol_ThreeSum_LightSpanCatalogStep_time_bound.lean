-- Prove2me | solution 1 for ThreeSum.LightSpanCatalogStep.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:47:51.057704+00:00
-- url     : https://prove2.me/submissions/f023f808-3f81-4b96-8824-fc5051fd8b70

import Definitions.Def_Submission_ThreeSum_LightSpanAxpy
import Definitions.Def_Submission_ThreeSum_LightSpanCatalogStep
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
open ThreeSum ThreeSum.LightSpanCatalogStep
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSpanCatalogStep
theorem _root_.solution (J p n : ℕ) :
    time J p n≤(p+1)*(n+1)*(J+1)*(LightPrimeCoefficient.mulAddTime p+500) := by
  let M := LightPrimeCoefficient.mulAddTime p
  let X := (J+1)*(M+500)
  have hinner : J*(M+150)+170≤X := by dsimp [X]; nlinarith
  have hx : 170≤X := by dsimp [X]; nlinarith
  have hb : n*(J*(M+150)+170)+170≤(n+1)*X := by
    calc
      _≤n*X+X := Nat.add_le_add (Nat.mul_le_mul_left n hinner) hx
      _=(n+1)*X := by ring
  have hy : 20≤(n+1)*X := by
    have hh := Nat.mul_le_mul_right X (show 1≤n+1 by omega)
    omega
  unfold time LightSpanCatalogBlock.time LightSpanAxpy.time
  change p*(n*(J*(M+150)+170)+170)+20≤(p+1)*(n+1)*(J+1)*(M+500)
  calc
    _≤p*((n+1)*X)+(n+1)*X := Nat.add_le_add (Nat.mul_le_mul_left p hb) hy
    _=_ := by dsimp [X]; ring
end ThreeSum.LightSpanCatalogStep
