-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ExcessPositive_proof_9cd724e3774f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:04:38.071191+00:00
-- url     : https://prove2.me/submissions/b82a65ab-c9ab-46c5-86f0-8ba5dfc28e74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivCycleEqZeroOfFormNotMem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_nonneg_953ee450d2f8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_zero_of_form_not_mem_884082b6d381
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleFiniteSupport_proof_010201f3d63e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleMul_proof_5282581d8898
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_congr_of_sub_mem_56ff166eaee6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace ExcessPositive
theorem _root_.solution : ExcessPositive.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD s hsP ⟨G, hϖG, hsG, hDG⟩
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hGdef : G ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant G := by
    by_contra h
    exact hsG (by unfold divCycle; rw [dif_neg h])
  have hGp : G.IsPrime := hGdef.1.1.1
  have hPG : P ≤ G := le_sup_left.trans hGdef.1.1.2
  obtain ⟨u, v, huG, huv⟩ := hD.2 G hGp hPG hGdef.2
  have huP : u ∉ P := fun h => huG (hPG h)
  have hfP := hD.1.num_not_mem
  have hgP := hD.1.den_not_mem
  have hvP : v ∉ P := by
    intro hv
    have h1 : u * f ∈ P := by
      have h2 := P.add_mem huv (P.mul_mem_right g hv)
      rwa [sub_add_cancel] at h2
    exact (hPp.mem_or_mem h1).elim huP hfP
  have hcyc : divCycle P (u * f) G = divCycle P (v * g) G :=
    congrFun (divCycle_congr_of_sub_mem huv) G
  have huf := congrFun (DivCycleMul.proof O K ι P u f hPp huP hfP) G
  have hvg := congrFun (DivCycleMul.proof O K ι P v g hPp hvP hgP) G
  simp only [Pi.add_apply] at huf hvg
  have hu0 := divCycle_eq_zero_of_form_not_mem P huG
  have hv0 := divCycle_nonneg P v G
  have hs0 := divCycle_nonneg P s G
  have hDpos : 0 < ratDiv P f g G := by
    unfold ratDiv at hDG ⊢
    omega
  have hprod : 0 < (divCycle P s G * ratDiv P f g G).toNat := by
    have : 0 < divCycle P s G * ratDiv P f g G := mul_pos (lt_of_le_of_ne hs0 (Ne.symm hsG)) hDpos
    omega

  have hfin := DivCycleFiniteSupport.proof.{u} O K ι P s
  have hbdd : BddAbove (Set.range fun G' : {G' : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G'} =>
      (divCycle P s G'.1 * ratDiv P f g G'.1).toNat) := by
    apply Set.Finite.bddAbove
    apply ((hfin.image fun G' => (divCycle P s G' * ratDiv P f g G').toNat).insert 0).subset
    rintro _ ⟨G', rfl⟩
    by_cases h : divCycle P s G'.1 = 0
    · left
      simp [h]
    · right
      exact ⟨G'.1, h, rfl⟩
  exact lt_of_lt_of_le hprod (le_ciSup hbdd ⟨G, hϖG⟩)
end ExcessPositive
end GroundTheory.Heights₂.Heights.NumbersDVR
