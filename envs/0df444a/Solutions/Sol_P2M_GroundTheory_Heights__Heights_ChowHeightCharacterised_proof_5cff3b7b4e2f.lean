-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowHeightCharacterised_proof_5cff3b7b4e2f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:28.074253+00:00
-- url     : https://prove2.me/submissions/2a6113cd-f5ce-4db8-8c84-2bcfd5a36cd8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PCharacterised
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_not_isChowForm_zero_1689bf6b18f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsMultiHomog_specFirst_e9679426b5b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHt_C_mul_prod_946e06149b1a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHt_zero_groups_eq_zero_bd0a7654af41
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_degrees_of_chowFormCycle_5abcefad6b58
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_mem_linForm_not_mem_e4689351a404
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_divCycle_3722b3dc77e4


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
open MvPolynomial MeasureTheory NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ChowHeightCharacterised
theorem _root_.solution (hR : ChowHeightRecursion.Statement)
    (hS : ChowFormSection.Statement) (hMul : ChowHeightMul.Statement) (hPt : ProjPrimeHasPoint.Statement) :
    ChowHeightCharacterised.Statement := by
  intro K _ _ n H J hJ e
  induction e with
  | zero =>
    intro δ I f hI hf hδ
    obtain ⟨u, -, hu⟩ := exists_mem_linForm_not_mem (K := K) hI.isRelevant (S := Set.univ)
      Submodule.span_univ
    obtain ⟨c, hc, g, hg, heq⟩ := hS K n 0 I f (fun j => (u j : K)) hI hf hu
    have hempty : (divCycle I fun j => (u j : K)).support = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro W hW
      exact not_isChowForm_zero hPt (isProjPrime_of_mem_support_divCycle hI _ hW) _ (hg W hW)
    rw [hJ 0 δ I f u hI hf hδ hu, hR K n 0 δ H I f u hI hf hδ hu, hempty, Finset.sum_empty]
    have hne : specFirst f (fun j => (u j : K)) ≠ 0 := by
      rw [heq, hempty, Finset.prod_empty, mul_one]
      exact C_ne_zero.mpr hc
    rw [chowHt_zero_groups_eq_zero H δ hne]
  | succ e ih =>
    intro δ I f hI hf hδ
    obtain ⟨u, -, hu⟩ := exists_mem_linForm_not_mem (K := K) hI.isRelevant (S := Set.univ)
      Submodule.span_univ
    obtain ⟨c, hc, g, hg, heq⟩ := hS K n (e + 1) I f (fun j => (u j : K)) hI hf hu
    rw [hJ (e + 1) δ I f u hI hf hδ hu, hR K n (e + 1) δ H I f u hI hf hδ hu]
    congr 1
    have hδs := hδ.specFirst (fun j => (u j : K))
    have hne : specFirst f (fun j => (u j : K)) ≠ 0 := by
      rw [heq]
      exact mul_ne_zero (C_ne_zero.mpr hc) (Finset.prod_ne_zero_iff.mpr fun W hW =>
        pow_ne_zero _ (hg W hW).1)
    rw [heq] at hδs hne
    obtain ⟨δW, hδW, hsum⟩ := exists_degrees_of_chowFormCycle (Nat.succ_pos e) _ c g hg hδs hne
    rw [heq, ← hsum, chowHt_C_mul_prod hMul H _ _ _ _ (fun W hW => (hg W hW).1) hc]
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [ih (δW W) W (g W) (isProjPrime_of_mem_support_divCycle hI _ hW) (hg W hW) (hδW W hW)]
end ChowHeightCharacterised
end GroundTheory.Heights₂.Heights
