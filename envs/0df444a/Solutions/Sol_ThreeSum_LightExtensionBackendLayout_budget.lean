-- Prove2me | solution 1 for ThreeSum.LightExtensionBackendLayout.budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:50:58.187785+00:00
-- url     : https://prove2.me/submissions/c1963edf-fba2-48cc-80c3-16e0d0bb1899

import Definitions.Def_Submission_ThreeSum_LightExtensionBackend
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuBudget
import Definitions.Def_Submission_ThreeSum_LightIrreducibleBudget
import Definitions.Def_Submission_ThreeSum_LightExtensionBackendLayout
import Theorems.Thm_ThreeSum_LightExtensionBackendLayout_end_le
import Theorems.Thm_ThreeSum_LightExtensionBackendLayout_ctx_slack
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
import Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_cell_word_after_ctx
import Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_seed_word_polynomial
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_factorTime_le_uniform
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_factorWord_le_uniform
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_program_length
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_uniformFactorWord_polynomial
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
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
attribute [local simp] ThreeSum.LightIrreducibleFinder.program_length
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionBackendLayout
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
variable {lim : Limits}
namespace ThreeSum.LightExtensionBackendLayout
theorem _root_.solution (base d p q J : ℕ) (hp : 1<p) (hd : 0<d) (hq : p^d=q)
    (hw : (lim.space : ℤ)≤lim.word)
    (hspace : base+reserve d p q J≤lim.space) :
    LightExtensionBackend.Budget lim (factor base d p q J)
      q (ctx base d) (ctx base d) (table base d) (logical base d q) (physical base d q J) J
      (a base d q J) (b base d q J) (h base d q J) (r base d q J) (prod base d q J) (sum base d q J)
      (LightIrreducibleFinder.uniformFactorTime d p q) := by
  let B := params d p q J
  have hB : 1≤B := by dsimp [B,params]; omega
  have hdB : d≤B := by dsimp [B,params]; omega
  have hpB : p≤B := by dsimp [B,params]; omega
  have hqB : q≤B := by dsimp [B,params]; omega
  have hJB : J≤B := by dsimp [B,params]; omega
  have hshort : d+p+q+2≤B := by dsimp [B,params]; omega
  have hseedshort : q+p+J+2≤B := by dsimp [B,params]; omega
  have h0 : 1≤B^4 := Nat.one_le_pow _ _ hB
  have h1 : B≤B^4 := by simpa using Nat.pow_le_pow_right hB (show 1≤4 by decide)
  have h2 : B^2≤B^4 := Nat.pow_le_pow_right hB (by decide)
  have h3 : B^3≤B^4 := Nat.pow_le_pow_right hB (by decide)
  have hReserve : ((base+reserve d p q J : ℕ) : ℤ)≤lim.word := (Int.ofNat_le.mpr hspace).trans hw
  have hSlack : ctx base d+2000000*B^4≤base+reserve d p q J := ctx_slack base d p q J
  have bound (x : ℕ) (hx : x≤ctx base d+2000000*B^4) : (x : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (hx.trans hSlack)).trans hReserve
  have hEnd := (end_le base d p q J).trans hspace
  have hFactorWord : LightIrreducibleFinder.uniformFactorWord d p q≤1000000*B^4 :=
    (LightIrreducibleFinder.uniformFactorWord_polynomial d p q hq).trans (by gcongr)
  have hDecode : LightCoefficientDecode.word (2*d) p (2*q) 0 1≤1000000*B^4 := by
    apply le_trans _ hFactorWord
    unfold LightIrreducibleFinder.uniformFactorWord
    omega
  have hTableWord : LightExtensionMultiplyTable.word q (ctx base d) p d base (a base d q J) (b base d q J)≤2000000*B^4 := by
    unfold LightExtensionMultiplyTable.word
    have hm : 30*(q*q+q+p+d+10)≤30*(B*B+B+B+B+10) := by gcongr
    apply hm.trans
    ring_nf
    omega
  have hSeedWord : LightExtensionSeedMatrix.word (J+2) q p≤2000000*B^4 := by
    apply (LightExtensionMenuMatrix.seed_word_polynomial q p J).trans
    have hh : (q+p+J+2)^3≤B^3 := by gcongr
    omega
  refine {
    finder := ?_
    targetCtx := by simp [factor,ctx]
    ctxTable := by simp [table]
    tableLogical := by simp [logical]
    logicalPhysical := by simp [physical]
    physicalA := by simp [a]
    aB := by simp [factor,b]
    bH := by simp [factor,h]
    hR := by simp [factor,r]
    rProduct := by simp [factor,prod]
    productSum := by simp [factor,sum]
    space := by simpa [factor] using hEnd
    tableWord := by simpa [factor] using bound _ (by omega)
    cellWord := ?_
    seedWord := by simpa [factor] using bound _ (show LightExtensionSeedMatrix.word (J+2) q p≤ctx base d+2000000*B^4 by omega) }
  · refine {
      qpos := by rw [←hq]; exact pow_pos (by omega) _
      primeBase := hp
      dimpos := hd
      ctxLeft := ?_
      powersTarget := by simp [factor,target]; omega
      targetCtx := by simp [factor,ctx]
      leftRight := by simp [factor]
      space := ?_
      factorWord := ?_
      searchWord := ?_
      controls := ?_
      decodeWord := by simpa [factor] using bound _ (by omega)
      factorTime := ?_ }
    · simp only [factor]
      unfold a physical logical table
      omega
    · simp only [factor]
      unfold sum prod r h b at hEnd
      omega
    · intro e he hed
      apply le_trans (Int.ofNat_le.mpr (LightIrreducibleFinder.factorWord_le_uniform
        (factor base d p q J) q e (by simpa [factor] using Nat.le_of_lt hp)
        (by simpa [factor] using Nat.le_of_lt hed) (by simpa [factor] using hq)))
      exact bound _ (by simpa [factor] using show LightIrreducibleFinder.uniformFactorWord d p q≤ctx base d+2000000*B^4 by omega)
    · change ((q*q+q+ctx base d+20 : ℕ) : ℤ)≤lim.word
      apply bound
      have hh : q*q≤B^2 := by nlinarith
      omega
    · change ((p+d+q+ctx base d+32 : ℕ) : ℤ)≤lim.word
      apply bound
      omega
    · intro e he hed
      exact LightIrreducibleFinder.factorTime_le_uniform (factor base d p q J) q e
        (by simpa [factor] using Nat.le_of_lt hp) (by simpa [factor] using Nat.le_of_lt hed)
        (by simpa [factor] using hq)
  · let C := LightExtensionBackend.quotientLayout (factor base d p q J)
      (a base d q J) (b base d q J) (h base d q J) (r base d q J) (prod base d q J) (sum base d q J)
    have hh := LightExtensionMenuMatrix.cell_word_after_ctx C q (ctx base d) (by simpa [C,LightExtensionBackend.quotientLayout,factor] using hq)
    apply bound
    change LightExtensionMultiplyCell.word C q (ctx base d)≤ctx base d+2000000*B^4
    apply hh.trans
    dsimp [C,LightExtensionBackend.quotientLayout,factor]
    gcongr <;> omega
end ThreeSum.LightExtensionBackendLayout
