-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_genDegAt_succ_b0303846c0e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:26.036469+00:00
-- url     : https://prove2.me/submissions/2d904535-e43f-4939-bd80-829381c7436b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogRenameCoordPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_coordPow_6706e34a9132
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_rename_coordPow_6db4fd2d12ff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_coordPow_not_mem_acb1a66812b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isSmoothHerm_pull_a18a49e18ba9

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
theorem _root_.solution (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement) (hInt : ArithmeticIntersectionIntegral.Statement)
    (I : AllFam) (hI : I.IsFamily) (n : ℕ) (ih : GenDegAt I n) : GenDegAt I (n + 1) := by
  intro K _ ι _ K' _ ι' _ κ v P' G J L L' hv hP' hP hJ hL hLL'
  have hrel := hP.2.1.2.2
  choose i hi using hrel
  have hPp : (imageZ v P').IsPrime := hP.2.1.1
  let α : K → ℕ := fun k => ((L (Fin.last n)).a k).toNat
  let β : K → ℕ := fun k => (-(L (Fin.last n)).a k).toNat
  have hfP := coordPow_not_mem hPp i hi α
  have hgP := coordPow_not_mem hPp i hi β
  have hfP' : rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) ∉ P' := fun h => hfP (Ideal.mem_comap.mpr h)
  have hgP' : rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ β k) ∉ P' := fun h => hgP (Ideal.mem_comap.mpr h)
  have hsec : IsRatSectionOn (imageZ v P') (L (Fin.last n)) (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k)
      (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ β k) :=
    ⟨α, β, isMultiHomog_coordPow i α, isMultiHomog_coordPow i β, hfP, hgP,
      fun k => Int.toNat_sub_toNat_neg _⟩
  have hsec' : IsRatSectionOn P' (L' (Fin.last n)) (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k))
      (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ β k)) := by
    refine ⟨_, _, isMultiHomog_rename_coordPow hv i α, isMultiHomog_rename_coordPow hv i β, hfP', hgP',
      fun k' => ?_⟩
    rw [(hLL' (Fin.last n)).1, pullDeg]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hv.1.extend_apply, hv.1.extend_apply, hv.1.extend_apply]
      exact Int.toNat_sub_toNat_neg _
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  have hL' : ∀ j, IsSmoothHerm (L' j) := fun j => isSmoothHerm_pull hv (hL j) (hLL' j)
  have e1 := hRat K' ι' (I K' ι') (hI K' ι') P' n (Fin.init L') (L' (Fin.last n)) _ _ hP'
    (fun j => hL' _) (hL' _) hsec'
  have e2 := hRat K ι (I K ι) (hI K ι) (imageZ v P') n (Fin.init L) (L (Fin.last n)) _ _ hP
    (fun j => hL _) (hL _) hsec
  rw [Fin.snoc_init_self] at e1 e2
  rw [e1, e2, recRRat, recRRat,
    hCyc I hI n ih K ι K' ι' κ v P' G J (Fin.init L) (Fin.init L') _ α hv hP' hP hJ (fun j => hL _)
      (fun j => hLL' _) (isMultiHomog_coordPow i α) hfP,
    hCyc I hI n ih K ι K' ι' κ v P' G J (Fin.init L) (Fin.init L') _ β hv hP' hP hJ (fun j => hL _)
      (fun j => hLL' _) (isMultiHomog_coordPow i β) hgP,
    hInt K ι K' ι' κ v P' n G J (Fin.init L) (Fin.init L') (L (Fin.last n)) (L' (Fin.last n)) _ _ hv hP' hP
      hJ (fun j => hL _) (fun j => hLL' _) (hL _) (hLL' _) hsec]
  ring
end GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
