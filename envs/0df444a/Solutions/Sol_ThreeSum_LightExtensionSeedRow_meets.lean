-- Prove2me | solution 1 for ThreeSum.LightExtensionSeedRow.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:21:13.972015+00:00
-- url     : https://prove2.me/submissions/3afa72ba-3dab-4a8e-974a-70ad25a74b49

import Definitions.Def_Submission_ThreeSum_LightCoefficientDecode
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow
import Theorems.Thm_ThreeSum_LightExtensionSeedRow_trajectory_lt
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_frame_append_zeros
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
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionSeedRow
open Light
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightExtensionSeedRow
theorem _root_.solution {proc pDigit pDivide table q p x y dst len : ℕ} (hp : P[proc]? = some (body pDigit))
    (hdigit : P[pDigit]? = some (LightRadixDigit.body pDivide)) (hdivide : P[pDivide]? = some LightSmallDivide.body)
    (μ : ℕ → ℤ) (mul : ℕ → ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 1 < lim.depth) (hx : x < q)
    (hy : y < q) (hmod : 0 < p) (htable : table + q * q ≤ dst) (hspace : dst + len ≤ lim.space)
    (hread : ∀ a < q, ∀ b < q, μ (table + a * q + b) = (mul a b : ℤ)) (hmul : ∀ a < q, ∀ b < q, mul a b < q)
    (hword : (word len q p : ℤ) ≤ lim.word) :
    Meets lim P proc depth [table, q, p, x, y, dst, len] μ (time len q)
      (fun z ν =>
        z = (trajectory mul x y len : ℤ) ∧
          (∀ i < len, ν (dst + i) = (((trajectory mul x y i) % p : ℕ) : ℤ)) ∧ SameOutside μ ν dst len) :=
  by
  have hb (z : ℕ) (hz : z ≤ word len q p) : (z : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hz).trans hword
  have hqWord := hb q (by unfold word; omega)
  have hpWord := hb p (by unfold word; omega)
  have hyWord := hb y (by unfold word; omega)
  have hxWord := hb x (by unfold word; omega)
  have h1 : (1 : ℤ) ≤ lim.word := by unfold word at hword; omega
  have hrun (i : ℕ) : trajectory mul x y i < q := trajectory_lt mul hx hy hmul i
  have hrunWord (i : ℕ) : (trajectory mul x y i : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.le_of_lt (hrun i))).trans hqWord
  apply Meets.of_body hp
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (y : ℕ) ?_ ?_ ?_
    on_goal -1 =>
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
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := len * (LightRadixDigit.time q + 100) + 6) (Q := Inv μ table q p x y dst len mul len)
        (Inv μ table q p x y dst len mul) len (LightRadixDigit.time q + 90) ?start ?round ?done ?bound)
      ?finish
  case start =>
    refine ⟨0, μ, ?_, ?_, SameOutside.refl⟩
    · simp only [trajectory]
      exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro i hi; omega
  case round =>
    rintro i _ hi _ ⟨old, ν, rfl, written, kept⟩
    have hz := hrun i
    have hzWord := hrunWord i
    have hnext := hrunWord (i + 1)
    have hm : trajectory mul x y i * q + x < q * q := by nlinarith
    have hprod : trajectory mul x y i * q ≤ q * q := by nlinarith
    have hprodWord := hb (trajectory mul x y i * q) (by unfold word; omega)
    have hread' : ν (table + trajectory mul x y i * q + x) = (trajectory mul x y (i + 1) : ℤ) :=
      by
      rw [kept _ (Or.inl (by omega)), hread _ hz x hx]
      rfl
    have hcallWord : (LightRadixDigit.word (trajectory mul x y i) 1 p : ℤ) ≤ lim.word :=
      by
      apply hb
      unfold LightRadixDigit.word word
      omega
    have htime : LightRadixDigit.time (trajectory mul x y i) ≤ LightRadixDigit.time q :=
      by
      unfold LightRadixDigit.time
      omega
    have hrem := Nat.mod_lt (trajectory mul x y i) hmod
    have hremWord := (Int.ofNat_le.mpr (Nat.le_of_lt hrem)).trans hpWord
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
      first
      |
        refine
          _root_.Light.Ends.callToThen
            ((LightRadixDigit.meets (d := depth + 1) (k := trajectory mul x y i) (b := 1) (p := p) hdigit hdivide ν
                (by omega) hcallWord)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (LightRadixDigit.meets (d := depth + 1) (k := trajectory mul x y i) (b := 1) (p := p) hdigit hdivide ν
              (by omega) hcallWord)
            ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightRadixDigit.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightRadixDigit.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightRadixDigit.time] <;> omega)
      on_goal -1 => (rintro val ν₁ ⟨hval, hν₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν₁
    have hv : val = (((trajectory mul x y i) % p : ℕ) : ℤ) := by simpa using hval
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + i) ((trajectory mul x y i) % p : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hv,
              LightRadixDigit.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hv, LightRadixDigit.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hv, LightRadixDigit.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    have haddr :
      ((table : ℤ) + (trajectory mul x y i : ℤ) * (q : ℤ) + (x : ℤ)).toNat = table + trajectory mul x y i * q + x := by
      norm_cast
    have hread'' (value : ℤ) :
      Function.update ν (dst + i) value (table + trajectory mul x y i * q + x) = (trajectory mul x y (i + 1) : ℤ) := by
      rw [Function.update_of_ne (by omega), hread']
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (trajectory mul x y (i + 1) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, haddr, hread'',
              LightRadixDigit.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [haddr, hread'', LightRadixDigit.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr, hread'', LightRadixDigit.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, val, Function.update ν (dst + i) (((trajectory mul x y i) % p : ℕ) : ℤ), by
        simp [update_frame_setLocal], ?_, kept.update ⟨by omega, by omega⟩ _⟩
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Function.update_of_ne (by omega)]
      exact written j hj
    · simp
  case done => rintro _ _ h; exact h
  case bound =>
    rintro i _ _ _ ⟨old, ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case finish =>
    rintro _ ⟨old, ν, rfl, written, kept⟩
    have hz := hrunWord len
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (trajectory mul x y len : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨rfl, written, kept⟩
end ThreeSum.LightExtensionSeedRow
