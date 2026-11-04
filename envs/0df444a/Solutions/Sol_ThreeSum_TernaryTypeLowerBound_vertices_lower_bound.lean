-- Prove2me | solution 1 for ThreeSum.TernaryTypeLowerBound.vertices_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:17.558123+00:00
-- url     : https://prove2.me/submissions/c43243a3-573a-4c6d-94dc-c60f2edfa3f9

import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_block_count_one
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_block_count_two
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_count_total
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_blockWord_injective
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeLowerBound
open Finset TernaryJointType TernaryCoverLocal
namespace ThreeSum.TernaryTypeLowerBound
theorem _root_.solution {L : ℕ} (π : DigitType)
    (htotal : π 0+π 1+π 2 = L) (hspace : 2*(π 1)+3*(π 2) ≤ L) :
    2^(π 1)*3^(π 2) ≤ (vertices L π).card := by
  classical
  let r := L-(2*(π 1)+3*(π 2))
  have hcard : Fintype.card (Fin L) = Fintype.card (BlockIndex (π 1) (π 2) r) := by
    simp [BlockIndex, r]
    omega
  let e : Fin L ≃ BlockIndex (π 1) (π 2) r := Fintype.equivOfCardEq hcard
  let f (c : BlockChoice (π 1) (π 2)) : TritWord L := blockWord c ∘ e
  have hcount (c : BlockChoice (π 1) (π 2)) (d : Fin 3) :
      digitCount (f c) d = count (blockWord (r := r) c) d :=
    Equiv.sum_comp e (fun i => if blockWord c i = d then 1 else 0)
  have hf (c : BlockChoice (π 1) (π 2)) : HasType (f c) π := by
    have h1 : digitCount (f c) 1 = π 1 := by rw [hcount, block_count_one]
    have h2 : digitCount (f c) 2 = π 2 := by rw [hcount, block_count_two]
    have hz := count_total (f c)
    change digitCount (f c) 0+digitCount (f c) 1+digitCount (f c) 2 = Fintype.card (Fin L) at hz
    rw [h1,h2,Fintype.card_fin] at hz
    have h0 : digitCount (f c) 0 = π 0 := by omega
    intro d
    fin_cases d
    · change digitCount (f c) 0 = π 0
      exact h0
    · change digitCount (f c) 1 = π 1
      exact h1
    · change digitCount (f c) 2 = π 2
      exact h2
  let g : BlockChoice (π 1) (π 2) → {q // q ∈ vertices L π} :=
    fun c => ⟨f c, mem_filter.mpr ⟨mem_univ _, hf c⟩⟩
  have hg : Function.Injective g := by
    intro c d h
    apply blockWord_injective (r := r)
    funext i
    have hh := congrFun (congrArg Subtype.val h) (e.symm i)
    simpa [g,f] using hh
  have h := Fintype.card_le_of_injective g hg
  simpa [BlockChoice, Fintype.card_fun] using h
end ThreeSum.TernaryTypeLowerBound
