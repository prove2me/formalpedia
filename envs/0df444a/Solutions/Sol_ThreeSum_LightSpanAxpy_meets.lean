-- Prove2me | solution 1 for ThreeSum.LightSpanAxpy.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:39.610945+00:00
-- url     : https://prove2.me/submissions/306a0c80-9905-4026-a090-94888dd30c8b

import Definitions.Def_Submission_ThreeSum_LightPrimeCoefficient
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightSpanAxpy
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_Light_wrote_rest
import Theorems.Thm_Light_wrote_succ
import Theorems.Thm_Light_wrote_zero
import Theorems.Thm_ThreeSum_LightPrimeCoefficient_mulAdd_meets
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
set_option autoImplicit false
open ThreeSum ThreeSum.LightSpanAxpy
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSpanAxpy
theorem _root_.solution {pMain pMulAdd pDivide src rowBase dst J a p d : ℕ} (hmain : P[pMain]? = some (body pMulAdd))
    (hmul : P[pMulAdd]? = some (LightPrimeCoefficient.mulAddBody pDivide))
    (hdivide : P[pDivide]? = some LightSmallDivide.body) (μ : ℕ → ℤ) (f row : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src + J ≤ dst) (hrow : rowBase + J ≤ dst) (hdst : dst + J ≤ lim.space) (hp : 0 < p) (ha : a < p)
    (hword : (LightPrimeCoefficient.word p : ℤ) ≤ lim.word) (hf : ∀ i < J, f i < p) (hr : ∀ i < J, row i < p)
    (hread : ∀ i < J, μ (src + i) = (f i : ℤ)) (hreadRow : ∀ i < J, μ (rowBase + i) = (row i : ℤ))
    (hd : d + 2 ≤ lim.depth) :
    Meets lim P pMain d [src, rowBase, dst, J, a, p] μ (time J p)
      (fun _ ν => (∀ i < J, ν (dst + i) = values f row a p i) ∧ SameOutside μ ν dst J) :=
  by
  have hsmall (x : ℕ) (hx : x < p) : (x : ℤ) ≤ lim.word :=
    by
    have hh : x ≤ LightPrimeCoefficient.word p := by unfold LightPrimeCoefficient.word; nlinarith
    exact (Int.ofNat_le.mpr hh).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv μ src rowBase dst J a p f row) J (LightPrimeCoefficient.mulAddTime p + 120) ?start ?round ?done ?bound
      (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, 0, 0, ?_⟩
    simp [Inv, update_frame_setLocal, wrote_zero]
    change frame [(src : ℤ), rowBase, dst, J, a, p, 0] = frame ([(src : ℤ), rowBase, dst, J, a, p, 0] ++ [0, 0, 0])
    exact (frame_append_zeros _ 3).symm
  case round =>
    rintro i _ hi _ ⟨x, y, z, rfl⟩
    let ν := wrote μ dst (values f row a p) i
    have hRead : ν (src + i) = (f i : ℤ) := by dsimp only [ν]; rw [wrote_rest (Or.inl (by omega)), hread i hi]
    have hRowRead : ν (rowBase + i) = (row i : ℤ) := by
      dsimp only [ν]
      rw [wrote_rest (Or.inl (by omega)), hreadRow i hi]
    have hF := hsmall (f i) (hf i hi)
    have hR := hsmall (row i) (hr i hi)
    have hMod := hsmall ((f i + a * row i) % p) (Nat.mod_lt _ hp)
    have hc := LightPrimeCoefficient.mulAdd_meets (d := d + 1) hmul hdivide ν (by omega) hp (hf i hi) ha (hr i hi) hword
    unfold roundBody
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (f i : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ν, hRead,
              LightPrimeCoefficient.mulAddTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [ν, hRead, LightPrimeCoefficient.mulAddTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ν, hRead,
              LightPrimeCoefficient.mulAddTime] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (row i : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ν, hRowRead,
              LightPrimeCoefficient.mulAddTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [ν, hRowRead, LightPrimeCoefficient.mulAddTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ν, hRowRead,
              LightPrimeCoefficient.mulAddTime] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
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
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ν,
              LightPrimeCoefficient.mulAddTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [ν, LightPrimeCoefficient.mulAddTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ν, LightPrimeCoefficient.mulAddTime] <;>
            omega)
      on_goal -1 => (rintro out ξ ⟨hout, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ξ
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + i) (values f row a p i) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hout, values,
              LightPrimeCoefficient.mulAddTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hout, values, LightPrimeCoefficient.mulAddTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hout, values,
              LightPrimeCoefficient.mulAddTime] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, (f i : ℤ), (row i : ℤ), out, ?_⟩
    simp [Inv, ν, update_frame_setLocal, wrote_succ]
  case done =>
    rintro _ _ ⟨x, y, z, rfl⟩
    exact ⟨fun i hi => wrote_done hi, fun x hx => wrote_rest hx⟩
  case bound =>
    rintro i _ hi _ ⟨x, y, z, rfl⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightSpanAxpy
