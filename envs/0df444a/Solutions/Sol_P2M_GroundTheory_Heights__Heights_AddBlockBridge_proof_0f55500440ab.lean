-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockBridge_proof_0f55500440ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:55:10.490459+00:00
-- url     : https://prove2.me/submissions/971f90df-ff21-4516-ba9d-c945df267ec8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_constMap_injective_f1a8d2f4aaab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_varT_ne_zero_0cfbfaa1a01e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_coneHom_X_aa17785c5646
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_mkF_e1a919750cdc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_ne_zero_of_isLive_fba38c539105
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_chartPow_8a3ea357af65
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_exists_chartRing_308442e990d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_of_reads_9f0e0ab7957e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_scale_injective_d67dd2591a0b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open AddBlockBridge
namespace GroundTheory.Heights₂.Heights
namespace AddBlockBridge
theorem _root_.solution (hCLS : ChartLatSection.Statement) : AddBlockBridge.Statement := by
  intro ι _ _ n Ω _ y P a m x' hP hx' hgen
  have hsec : ∀ j, ∃ t : IntegralSection P a, P.Reads y a (x' j) t.toFun := fun j ↦ by
    obtain ⟨t, ht⟩ := (hCLS ι n Ω y P a 1 (x' j) hP).mp (hx' j)
    refine ⟨t.cast (one_smul ℕ a), ?_⟩
    rw [show P.Reads y a = P.Reads y ((1 : ℕ) • a) by rw [one_smul]]
    exact ht
  choose t ht using hsec
  have hval : ∀ j, funHom P y hP (t j).toFun = constMap ι (x' j) * ∏ k, varT k ^ a k :=
    fun j ↦ funHom_of_reads P y hP (t j) (ht j)

  have hquot : ∀ c, P.IsLive c → ∀ j, funHom P y hP ((t j).toFun / P.chartPow c a) =
      constMap ι (x' j * ∏ k, y ⟨k, c k⟩ ^ (-a k)) := by
    intro c hc j
    have hy : ∀ k, constMap ι (y ⟨k, c k⟩) ≠ 0 := fun k ↦
      (map_ne_zero_iff _ constMap_injective).mpr (ne_zero_of_isLive P y hP hc k)
    have hT : ∏ k, varT (Ω := Ω) k ^ a k ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (varT_ne_zero k)
    have hY : ∏ k, constMap ι (y ⟨k, c k⟩) ^ a k ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (hy k)
    have e : ∏ k, constMap ι (y ⟨k, c k⟩ ^ (-a k)) = (∏ k, constMap ι (y ⟨k, c k⟩) ^ a k)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [map_zpow₀, zpow_neg]
    rw [map_div₀, hval, funHom_chartPow, map_mul, map_prod, e]
    field_simp
  have hmem : ∀ c, P.IsLive c → ∀ j, (t j).toFun / P.chartPow c a ∈ P.chartRing c := by
    intro c hc j
    have hm := hx' j c (ne_zero_of_isLive P y hP hc)
    simp only [Nat.cast_one, one_mul] at hm
    obtain ⟨η, hη, he⟩ := exists_chartRing P y hP c hm
    rwa [(funHom P y hP).injective ((hquot c hc j).trans he.symm)]
  have hgen' : ∀ c, P.IsLive c → ∃ u : Fin (m + 1) → P.FunField, (∀ j, u j ∈ P.chartRing c) ∧
      ∑ j, u j * ((t j).toFun / P.chartPow c a) = 1 := by
    intro c hc
    obtain ⟨u, hu, hsum⟩ := hgen c (ne_zero_of_isLive P y hP hc)
    choose v hv hve using fun j ↦ exists_chartRing P y hP c (hu j)
    refine ⟨v, hv, (funHom P y hP).injective ?_⟩
    rw [map_sum, map_one, ← map_one (constMap (Ω := Ω) ι), ← hsum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_mul, hve j, hquot c hc j]
  let D : AddBlockData P :=
    { deg := a
      size := m
      elt := fun j ↦ (t j).toFun
      elt_deg := fun j ↦ ⟨(t j).num, (t j).den, (t j).numDeg, (t j).denDeg, (t j).num_isHomogeneous,
        (t j).den_isHomogeneous, (t j).deg_eq, (t j).den_not_mem, rfl⟩
      chart_mem := hmem
      generating := hgen' }

  let w : Option ι → ConeField ι Ω := fun o ↦ o.elim (∏ k, varT k ^ a k) varT
  have hw : ∀ o, w o ≠ 0 := by
    rintro (_ | k)
    · exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (varT_ne_zero k)
    · exact varT_ne_zero k
  let σ : MvPolynomial (Option ι) (ConeField ι Ω) →ₐ[ConeField ι Ω] MvPolynomial (Option ι) (ConeField ι Ω) :=
    aeval fun o ↦ C (w o) * X o
  have hcomp : (map (funHom P y hP)).comp D.extMap = σ.toRingHom.comp
      ((map (constMap ι)).comp (Geo.mConeMap (ι := blockIdx D.extSizes) (D.plusCoord y x')).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ by simp) fun v ↦ ?_
    rcases v with ⟨_ | k, i⟩
    · simp [D, σ, w, AddBlockData.extMap, AddBlockData.extVal, Geo.mConeMap, AddBlockData.plusCoord]
      rw [show (funHom P y hP) (t i).toFun = _ from hval i, map_mul, map_prod]
      ring
    · simp [D, σ, w, AddBlockData.extMap, AddBlockData.extVal, Geo.mConeMap, AddBlockData.plusCoord,
        funHom_mkF, coneHom_X]
      ring
  have hread : D.BlockReading y x' :=
    { ideal_eq := hP
      ext_eq := by
        ext f
        rw [AddBlockData.extIdeal, Geo.mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker]
        have hf := congrArg (fun ψ ↦ ψ f) hcomp
        simp only [RingHom.comp_apply] at hf
        constructor
        · intro h
          rw [h, map_zero] at hf
          have h2 := scale_injective w hw (hf.symm.trans (map_zero σ).symm)
          exact map_injective _ constMap_injective (h2.trans (map_zero _).symm)
        · intro h
          refine map_injective _ (funHom P y hP).injective ?_
          rw [hf, map_zero]
          simp [h]
      reads := ht }
  exact ⟨D, rfl, rfl, hread⟩
end AddBlockBridge
end GroundTheory.Heights₂.Heights
