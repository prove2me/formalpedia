-- Prove2me | solution 1 for ThreeSum.LightOneHot.setup_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:17.6288+00:00
-- url     : https://prove2.me/submissions/d4c2a5c1-2adb-4870-afc8-68d714b776be

import Definitions.Def_Submission_ThreeSum_OneHotMask
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightOneHot
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
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
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightOneHot
open Light ThreeSum.OneHotMask ThreeSum.LightSubsetAddress
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightOneHot
theorem _root_.solution {pMain pPowers pHash : ℕ} (hmain : P[pMain]? = some (setupBody pPowers pHash))
    (hpowers : P[pPowers]? = some powTableBody) (hhash : P[pHash]? = some (body pHash)) {μ : ℕ → ℤ}
    {L m src0 src1 work U d : ℕ} (w0 w1 : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hspace : work + (L + 1) ≤ lim.space)
    (hsrc0 : src0 + L ≤ work) (hsrc1 : src1 + L ≤ work) (hword : (word L U : ℤ) ≤ lim.word) (hm : m < 2 ^ L)
    (hd : d + L + 1 ≤ lim.depth) (hread0 : ∀ i < L, μ (src0 + i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1 + i) = (w1 i : ℤ)) (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim P pMain d [L, m, src0, src1, work] μ (setupTime L)
      (fun r μ' => r = (OneHotMask.eval w0 w1 L m : ℤ) ∧ Powers μ' work L ∧ SameOutside μ μ' work (L + 1)) :=
  by
  have hpBound : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : 2 ^ (L + 1) ≤ word L U := by unfold word; omega
    exact (by exact_mod_cast hh : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ (word L U : ℤ)).trans hword
  have hbase : (2 : ℤ) ≤ lim.word :=
    by
    have hh : (2 ^ 1 : ℕ) ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hz : (2 : ℤ) ≤ ((2 ^ (L + 1) : ℕ) : ℤ) := by exact_mod_cast hh
    exact hz.trans hpBound
  apply Meets.of_body hmain
  unfold setupBody setupTime
  have hpow :=
    powTable_meets (d := d + 1) (μ := μ) (dst := work) (L := L + 1) (b := 2) hpowers hw hspace
      (by
        intro j hj
        have hh : (2 ^ j : ℕ) ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by decide) hj
        exact (by exact_mod_cast hh : ((2 ^ j : ℕ) : ℤ) ≤ ((2 ^ (L + 1) : ℕ) : ℤ)).trans hpBound)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hpow _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hpow ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, time] <;> omega)
    on_goal -1 => (rintro _ μ₁ ⟨hpowSeg, hsame⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcall :=
    meets (W := L) (powers := work) (src0 := src0) (src1 := src1) (U := U) hhash μ₁ w0 w1 hw hspace (by omega)
      (by omega) hword (powers_of_segment hpowSeg)
      (by intro i hi; rw [hsame (src0 + i) (Or.inl (by omega))]; exact hread0 i hi)
      (by intro i hi; rw [hsame (src1 + i) (Or.inl (by omega))]; exact hread1 i hi) hbound0 hbound1 L m le_rfl hm
      (d + 1) (by omega)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, time] <;> omega)
    on_goal -1 => (rintro res μ₂ ⟨hres, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₂
  exact ⟨by simpa using hres, powers_of_segment hpowSeg, hsame⟩
end ThreeSum.LightOneHot
