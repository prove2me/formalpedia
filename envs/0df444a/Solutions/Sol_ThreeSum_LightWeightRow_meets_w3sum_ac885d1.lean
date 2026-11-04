-- Prove2me | solution 1 for ThreeSum.LightWeightRow.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:35:54.41821+00:00
-- url     : https://prove2.me/submissions/4057d92f-28c2-47d8-869c-68d678a95e48

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
import Definitions.Def_Submission_ThreeSum_LightWeightRow
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
open ThreeSum ThreeSum.LightWeightRow
open Light
set_option maxHeartbeats 1200000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightWeightRow
theorem _root_.solution {pMain pDigit pDivide : ℕ} (hmain : P[pMain]? = some (body pDigit))
    (hdigit : P[pDigit]? = some (LightRadixDigit.body pDivide)) (hdivide : P[pDivide]? = some LightSmallDivide.body)
    {μ : ℕ → ℤ} {W p k powers start stride dst n : ℕ} (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth)
    (hp : 1 ≤ p) (hspace : dst + n ≤ lim.space) (hpowers : powers + (W + 1) ≤ lim.space)
    (hsep : Apart powers (W + 1) dst n) (hword : (word W p k start stride : ℤ) ≤ lim.word)
    (hcoords : ∀ i < n, start + stride * i < W) (hread : ∀ e ≤ W, μ (powers + e) = ((p ^ e : ℕ) : ℤ)) :
    Meets lim P pMain d [W, p, k, powers, start, stride, dst, n] μ (time n k)
      (fun _ μ' =>
        (∀ i < n, μ' (dst + i) = (WeightEnumeration.digit p W k (start + stride * i) : ℤ)) ∧ SameOutside μ μ' dst n) :=
  by
  have hbudget (x : ℕ) (hx : x ≤ word W p k start stride) : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hkWord := hbudget k (by unfold word; omega)
  have hpWord := hbudget p (by unfold word; omega)
  have hstrideWord := hbudget stride (by unfold word; omega)
  have hstartWord := hbudget start (by unfold word; omega)
  have hWWord := hbudget W (by unfold word; omega)
  have h1Word := hbudget 1 (by unfold word; omega)
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ W p k powers start stride dst n) n (LightRadixDigit.time k + 92) ?_ ?_ ?_ ?_
  · refine ⟨0, μ, ?_, ?_, SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro i hi; omega
  · rintro i _ hi _ ⟨r, μ', rfl, written, kept⟩
    have hc := hcoords i hi
    let e := W - 1 - (start + stride * i)
    have he : e ≤ W := by unfold e; omega
    have hpbound : p ^ e ≤ p ^ (W + 1) := Nat.pow_le_pow_right hp (by omega)
    have hpWord' := hbudget (p ^ e) (by unfold word; omega)
    have hmulWord : (stride : ℤ) * i ≤ lim.word :=
      by
      have hh : stride * i ≤ W := by omega
      exact (by exact_mod_cast hh : (stride : ℤ) * i ≤ (W : ℤ)).trans hWWord
    have hmulNonneg : (0 : ℤ) ≤ (stride : ℤ) * i := by positivity
    have hcZ : (start : ℤ) + (stride : ℤ) * i < W := by exact_mod_cast hc
    have hsub : (W : ℤ) - 1 - ((start : ℤ) + (stride : ℤ) * i) = (e : ℤ) :=
      by
      have hs : e + (start + stride * i) + 1 = W := by unfold e; omega
      have hsZ : (e : ℤ) + ((start : ℤ) + (stride : ℤ) * i) + 1 = W := by exact_mod_cast hs
      omega
    have haddr : ((powers : ℤ) + ((W : ℤ) - 1 - ((start : ℤ) + (stride : ℤ) * i))).toNat = powers + e := by
      rw [hsub, ← Nat.cast_add, Int.toNat_natCast]
    have hpower : μ' (powers + e) = ((p ^ e : ℕ) : ℤ) :=
      by
      rw [kept _ (by omega)]
      exact hread e he
    have hcallWord : (LightRadixDigit.word k (p ^ e) p : ℤ) ≤ lim.word :=
      by
      apply hbudget
      unfold LightRadixDigit.word word
      omega
    have hcall :=
      LightRadixDigit.meets (d := d + 1) (k := k) (b := p ^ e) (p := p) hdigit hdivide μ' (by omega) hcallWord
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
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, haddr, hsub, hpower,
              e, LightRadixDigit.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [haddr, hsub, hpower, e, LightRadixDigit.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr, hsub, hpower, e,
              LightRadixDigit.time] <;>
            omega)
      on_goal -1 => (rintro value μ₁ ⟨hvalue, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ₁
    have hv : value = (WeightEnumeration.digit p W k (start + stride * i) : ℤ) := hvalue
    have hvBound : WeightEnumeration.digit p W k (start + stride * i) ≤ k :=
      (Nat.mod_le _ _).trans (Nat.div_le_self _ _)
    have hvWord : (WeightEnumeration.digit p W k (start + stride * i) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr hvBound).trans hkWord
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + i) (WeightEnumeration.digit p W k (start + stride * i) : ℕ) ?_ ?_ ?_
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
    refine
      ⟨by simp, value, Function.update μ' (dst + i) (WeightEnumeration.digit p W k (start + stride * i) : ℤ), by
        simp [update_frame_setLocal], ?_, kept.update ⟨by omega, by omega⟩ _⟩
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Function.update_of_ne (by omega)]
      exact written j hj
    · simp
  · rintro _ _ ⟨r, μ', rfl, written, kept⟩
    exact ⟨written, kept⟩
  · rintro i _ _ _ ⟨r, μ', rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightWeightRow
