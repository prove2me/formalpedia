-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPolynomial.atomExpr_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:35:52.227612+00:00
-- url     : https://prove2.me/submissions/5c42d227-aa9a-4796-9378-65b2172ffb89

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_tensorIndex_lt
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_prodCircuits
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_sumCircuits
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
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
open ThreeSum ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPolynomial
theorem _root_.solution (m base Λ colsBase : ℕ) (cols : PairedIndex m → ℕ) (μ : ℕ → ℤ) {lim : Limits} (hΛ : 1 ≤ Λ)
    (hbound : ∀ r, cols r < Λ) (hcols : ∀ r, μ (colsBase + (Fintype.equivFin (PairedIndex m) r).val) = (cols r : ℤ))
    (hTspace : base + Λ ^ 4 ≤ lim.space) (hCspace : colsBase + Fintype.card (PairedIndex m) ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (q : Quad m) : (atomExpr m q).Safe lim ⟨frame [base, Λ, colsBase], μ⟩ :=
  by
  let a := cols q.1
  let b := cols q.2.1
  let c := cols q.2.2.1
  let e := cols q.2.2.2
  have ha : a < Λ := hbound _
  have hb : b < Λ := hbound _
  have hc : c < Λ := hbound _
  have he : e < Λ := hbound _
  have h₁ : a * Λ + b < Λ ^ 2 := by nlinarith
  have h₂ : (a * Λ + b) * Λ + c < Λ ^ 3 := by nlinarith
  have h₃ : ((a * Λ + b) * Λ + c) * Λ + e < Λ ^ 4 := tensorIndex_lt ha hb hc he
  have hpow₁ : Λ ≤ Λ ^ 4 := by simpa using Nat.pow_le_pow_right hΛ (by decide : 1 ≤ 4)
  have hpow₂ : Λ ^ 2 ≤ Λ ^ 4 := Nat.pow_le_pow_right hΛ (by decide : 2 ≤ 4)
  have hpow₃ : Λ ^ 3 ≤ Λ ^ 4 := Nat.pow_le_pow_right hΛ (by decide : 3 ≤ 4)
  have hread₁ := hcols q.1
  have hread₂ := hcols q.2.1
  have hread₃ := hcols q.2.2.1
  have hread₄ := hcols q.2.2.2
  have hind₁ := (Fintype.equivFin (PairedIndex m) q.1).isLt
  have hind₂ := (Fintype.equivFin (PairedIndex m) q.2.1).isLt
  have hind₃ := (Fintype.equivFin (PairedIndex m) q.2.2.1).isLt
  have hind₄ := (Fintype.equivFin (PairedIndex m) q.2.2.2).isLt
  have hnatword (x : ℕ) (hx : x ≤ lim.space) : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hw
  have hΛWord := hnatword Λ (by omega)
  have h₁word := hnatword (a * Λ + b) (by omega)
  have h₂word := hnatword ((a * Λ + b) * Λ + c) (by omega)
  have h₃word := hnatword (((a * Λ + b) * Λ + c) * Λ + e) (by omega)
  have hmul₁ := hnatword (a * Λ) (by omega)
  have hmul₂ := hnatword ((a * Λ + b) * Λ) (by omega)
  have hmul₃ := hnatword (((a * Λ + b) * Λ + c) * Λ) (by omega)
  dsimp [a, b, c, e] at *
  push_cast at h₁word h₂word h₃word hmul₁ hmul₂ hmul₃
  have hn₁ : (0 : ℤ) ≤ (cols q.1 : ℤ) * Λ := by positivity
  have hn₂ : (0 : ℤ) ≤ ((cols q.1 : ℤ) * Λ + cols q.2.1) * Λ := by positivity
  have hn₃ : (0 : ℤ) ≤ (((cols q.1 : ℤ) * Λ + cols q.2.1) * Λ + cols q.2.2.1) * Λ := by positivity
  have haddr : base + tensorIndex Λ (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2) < lim.space :=
    (Nat.add_lt_add_left (tensorIndex_lt ha hb hc he) base).trans_le hTspace
  have haddrZ : (base : ℤ) + ((((cols q.1 : ℤ) * Λ + cols q.2.1) * Λ + cols q.2.2.1) * Λ + cols q.2.2.2) < lim.space :=
    by simpa [tensorIndex, Nat.cast_add, Nat.cast_mul] using (Int.ofNat_lt.mpr haddr)
  unfold atomExpr
  ( (try have := _root_.Light.Std.space_le (by assumption))
    (try have := _root_.Light.Std.const_le (by assumption))
    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread₁, hread₂, hread₃, hread₄] <;> omega)
end ThreeSum.LightTernaryPairedPolynomial
