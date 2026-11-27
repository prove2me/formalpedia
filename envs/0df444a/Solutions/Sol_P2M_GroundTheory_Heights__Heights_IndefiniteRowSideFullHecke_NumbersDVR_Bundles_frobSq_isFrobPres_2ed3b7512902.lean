-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_frobSq_isFrobPres_2ed3b7512902
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:00:17.488469+00:00
-- url     : https://prove2.me/submissions/4ccd83d8-9a41-4ff6-ba8c-d82d2a97d9cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ScaledRankOneLeStandardRankOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_mem_standardRankOne_e1c44e101352
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_mem_scaledRankOne_7d4f94ad393c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_gG_sq_071b42a7ab7e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_uG_isUnit_ea22499839b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_clR_coe_bde0721187b8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
local notation "ΩG" => FractionRing GaussianInt
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
theorem _root_.solution :
    IsFrobPres GO 2 (ptCoord (Ω := ΩG)) (std1 GO ptCoord) (sc1 GO ptCoord gG (GO_frac_ne gG gG_ne_zero))
      (std1 GO ptCoord) (sc1 GO ptCoord 2 (GO_frac_ne 2 two_ne_zero)) frobSq := by
  have hT : (algebraMap GO ΩG 2) = 2 := map_ofNat _ 2
  have h2 : (2 : ΩG) ≠ 0 := by rw [← hT]; exact GO_frac_ne 2 two_ne_zero
  have hG := GO_frac_ne gG gG_ne_zero
  have hG2 : algebraMap GO ΩG gG ^ 2 = algebraMap GO ΩG uG * 2 := by
    rw [← map_pow, gG_sq, map_mul, Nat.cast_ofNat, map_ofNat]
  refine ⟨fun s _ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro v hv
    rw [mem_standardRankOne] at hv ⊢
    exact pow_mem hv 2
  · intro v hv
    rw [mem_scaledRankOne] at hv ⊢
    rw [hT]
    have hU : algebraMap GO ΩG uG ≠ 0 := GO_frac_ne uG uG_isUnit.ne_zero
    have key : (2 : ΩG)⁻¹ * frobSq s v 0 =
        algebraMap GO ΩG uG * ((algebraMap GO ΩG gG)⁻¹ * v 0) ^ 2 := by
      rw [mul_pow, inv_pow, hG2]
      simp only [frobSq]
      field_simp
    rw [key]
    exact mul_mem (Subalgebra.algebraMap_mem _ uG) (pow_mem hv 2)
  · intro v hv w hw
    rw [mem_standardRankOne] at hv hw
    rw [mem_scaledRankOne, hT]
    have key : (2 : ΩG)⁻¹ * (frobSq s (v + w) - frobSq s v - frobSq s w) 0 = v 0 * w 0 := by
      simp only [frobSq, Pi.sub_apply, Pi.add_apply]
      field_simp
      ring
    rw [key]
    exact mul_mem hv hw
  · intro a _ v _
    rw [mem_scaledRankOne, hT]
    simp [frobSq, mul_pow]
  · intro v hv
    rw [mem_standardRankOne] at hv
    rw [mem_scaledRankOne, hT]
    simpa [← mul_assoc, inv_mul_cancel₀ h2] using hv
  · intro Nm _ _ hkill χ hadd hker hsemi
    have he1 : (fun _ => (1 : ΩG)) ∈ (std1 GO (ptCoord (Ω := ΩG))).lat s :=
      (mem_standardRankOne GO).mpr (one_mem _)
    have hk2 : ∀ n : Nm, (2 : chartRing GO (mseg (ptCoord (Ω := ΩG))) s) • n = 0 := by
      intro n
      have := hkill n
      rwa [Nat.cast_ofNat] at this
    have c2 : ((2 : chartRing GO (mseg (ptCoord (Ω := ΩG))) s) : ΩG) = 2 :=
      map_ofNat (chartRing GO (mseg (ptCoord (Ω := ΩG))) s).val 2
    have h2R : (2 : ΩG) ∈ chartRing GO (mseg (ptCoord (Ω := ΩG))) s := by
      rw [← hT]
      exact Subalgebra.algebraMap_mem _ 2
    have hψe1 : frobSq s (fun _ => (1 : ΩG)) = fun _ => 1 := by
      funext k
      simp [frobSq]
    refine ⟨fun w => clR s (w 0) • χ (fun _ => 1), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro v hv w hw
      rw [mem_standardRankOne] at hv hw
      dsimp only
      rw [← add_smul]
      congr 1
      apply Subtype.ext
      simp only [Pi.add_apply, Subalgebra.coe_add]
      rw [clR_coe (add_mem hv hw), clR_coe hv, clR_coe hw]
    · intro w hw
      rw [mem_scaledRankOne, hT] at hw
      have hw0 : w 0 ∈ chartRing GO (mseg (ptCoord (Ω := ΩG))) s := by
        have h := mul_mem h2R hw
        rwa [← mul_assoc, mul_inv_cancel₀ h2, one_mul] at h
      have hsplit : clR s (w 0) = 2 * clR s ((2 : ΩG)⁻¹ * w 0) := by
        apply Subtype.ext
        rw [Subalgebra.coe_mul, c2, clR_coe hw0, clR_coe hw]
        field_simp
      show clR s (w 0) • χ _ = 0
      rw [hsplit, mul_smul, hk2]
    · intro a w hw
      rw [mem_standardRankOne] at hw
      have hm : ((a : ΩG) • w) 0 ∈ chartRing GO (mseg (ptCoord (Ω := ΩG))) s := by
        simpa using mul_mem a.2 hw
      show clR s (((a : ΩG) • w) 0) • χ _ = a • (clR s (w 0) • χ _)
      rw [← mul_smul]
      congr 1
      apply Subtype.ext
      rw [clR_coe hm, Subalgebra.coe_mul, clR_coe hw]
      simp
    · intro v hv
      have hv0 := (mem_standardRankOne GO).mp hv
      have hv' : v = ((⟨v 0, hv0⟩ : chartRing GO (mseg (ptCoord (Ω := ΩG))) s) : ΩG) •
          (fun _ => (1 : ΩG)) := by
        funext k
        fin_cases k
        simp
      show clR s (frobSq s v 0) • χ _ = χ v
      conv_rhs => rw [hv', hsemi _ _ he1]
      congr 1
      apply Subtype.ext
      rw [clR_coe (by simpa [frobSq] using pow_mem hv0 2)]
      simp [frobSq]
    · intro lam' hlam' hcomp w hw
      have hw0 := (mem_standardRankOne GO).mp hw
      have hw' : w = ((⟨w 0, hw0⟩ : chartRing GO (mseg (ptCoord (Ω := ΩG))) s) : ΩG) •
          (fun _ => (1 : ΩG)) := by
        funext k
        fin_cases k
        simp
      have hl1 : lam' (fun _ => 1) = χ (fun _ => 1) := by
        have := hcomp _ he1
        rwa [hψe1] at this
      show lam' w = clR s (w 0) • χ _
      rw [hw', hlam'.2.2 _ _ he1, hl1]
      congr 1
      apply Subtype.ext
      rw [clR_coe (by simpa using hw0)]
      simp
  · intro s t _ _ v _ m _
    refine ⟨0, ?_⟩
    simp only [mseg_of_one ptCoord_eq, div_one, one_pow, one_smul]
    rw [show frobSq t v = frobSq s v from rfl, sub_self]
    exact zero_mem _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
