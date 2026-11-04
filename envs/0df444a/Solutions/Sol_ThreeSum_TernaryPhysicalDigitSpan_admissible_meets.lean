-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalDigitSpan.admissible_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:58.512883+00:00
-- url     : https://prove2.me/submissions/706dc836-b24f-4712-b0c1-f82bde369c2c

import Definitions.Def_Submission_ThreeSum_LightStoredSpan
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_physical_span_iff
import Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_flag_menu_iff
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightStoredSpan_program_length
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightStoredSpan.program_length
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog


attribute [local simp] ThreeSum.TernaryPhysicalDigitSpan.flag_menu_iff

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalDigitSpan
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] {J : ℕ}
variable {E : Type*} [Field E] [Algebra K E] [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryPhysicalDigitSpan
theorem _root_.solution {lim : Limits} {P : Program}
    {pMain pEq catalog n candidate depth : ℕ}
    (hmain : P[pMain]?=some (LightSpanCatalogTest.body pEq))
    (heq : P[pEq]?=some LightSpanRowEqual.body)
    (μ : ℕ → ℤ) (f : ℕ → ℕ → ℕ) (row : Fin (J+2) → ZMod p)
    (rows : List (Fin J → ZMod p))
    (H : TernaryStoredSpan.Represents f n (rows.map (reversal J)))
    (hw : (lim.space : ℤ)≤lim.word) (hcat : catalog+J*n≤lim.space)
    (hrow : candidate+J≤lim.space)
    (hcontrols : ((n+J+16 : ℕ) : ℤ)≤lim.word) (hpp : (p : ℤ)≤lim.word)
    (hf : ∀k<n, ∀i<J, f k i<p)
    (hread : ∀k<n, ∀i<J, μ (catalog+J*k+i)=(f k i : ℤ))
    (hreadRow : ∀i<J, μ (candidate+i)=(LightStoredSpan.rowValues (physicalDigits row) i : ℤ))
    (hd : depth+1≤lim.depth) :
    Meets lim P pMain depth [catalog,n,J,candidate] μ (LightSpanCatalogTest.time J n)
      (fun r ν => (r=1 ↔ row∉forbidden rows) ∧ ν=μ) := by
  have hh := LightStoredSpan.admissible_meets hmain heq μ f (physicalDigits row)
    (rows.map (reversal J)) H hw hcat hrow hcontrols hpp hf hread hreadRow hd
  apply hh.mono le_rfl
  intro r ν h
  refine ⟨?_,h.2⟩
  rw [h.1]
  have hflag : LightStoredSpan.admissibleFlag (rows.map (reversal J)) (physicalDigits row)=1 ↔ row∉forbidden rows := by
    rw [LightStoredSpan.admissibleFlag_eq_one]
    exact not_congr (physical_span_iff rows row)
  simpa only [Nat.cast_eq_one] using hflag
end ThreeSum.TernaryPhysicalDigitSpan
